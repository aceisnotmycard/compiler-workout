open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
        
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
   match insn with
      | BINOP op ->
        let y::x::tail = stack in 
        eval env (cstack, (Value.of_int (Expr.to_func op (Value.to_int x) (Value.to_int y))) :: tail, c) prg'
      | CONST i  -> eval env (cstack, (Value.of_int i)::stack, c) prg'
      | STRING str -> eval env (cstack, (Value.of_string str)::stack, c) prg'
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) prg'
      | ST x     -> let z::tail = stack in 
        eval env (cstack, tail, (State.update x z st, i, o)) prg'
      | STA (x, count) -> let v::indices, stack' = split (count + 1) stack in
        eval env (cstack, stack', (Language.Stmt.update st x v (List.rev indices), i, o)) prg'
      | LABEL _ -> eval env conf prg'
      | JMP label -> eval env conf (env#labeled label)
      | CJMP (cond, label) -> let (Value.Int x) :: tail = stack in
        eval env (cstack, tail, c) (if (cond = "nz" && x != 0 || cond = "z" && x = 0)
                                        then (env#labeled label) else prg')
      | BEGIN (_, args, local_vars) ->
        let current_state = State.enter st (args @ local_vars) in
        let (res_state, res_stack) = List.fold_right 
          (fun arg (st, v::tail) -> (State.update arg v st, tail)) args (current_state, stack) in
        eval env (cstack, res_stack, (res_state, i, o)) prg'
      | CALL (name, n, p) -> 
        (if env#is_label name then 
          eval env ((prg', st)::cstack, stack, c) (env#labeled name)
         else eval env (env#builtin conf name n p) prg'
        )
      | END | RET _ ->
        match cstack with
        | (ss, s) :: tail -> eval env (tail, stack, (State.leave st s, i, o)) ss        
        | [] -> conf

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let labelGenerator =
  object
    val mutable count = 0
    method gen =
        count <- count + 1;
        "label_" ^ string_of_int count
    end

let rec compile_expr = function
    | Expr.Const c -> [CONST c]
    | Expr.Array array -> 
      List.flatten (List.map compile_expr array) @ 
      [CALL ("$array", List.length array, false)]
    | Expr.String str -> [STRING str]
    | Expr.Var v -> [LD v]
    | Expr.Binop (op, expr1, expr2) -> 
      (compile_expr expr1) @ 
      (compile_expr expr2) @ 
      [BINOP op]
    | Expr.Elem (arr, idx) -> compile_expr arr @ compile_expr idx @ [CALL ("$elem", 2, false)]
    | Expr.Length l -> compile_expr l @ [CALL ("$length", 1, false)]
    | Expr.Call (name, args) -> 
      List.concat (List.map compile_expr args) @ 
      [CALL (name, List.length args, false)]


let rec compile' = function
    | Stmt.Assign (name, args, expr) -> (match args with 
      | [] -> compile_expr expr @ [ST name]
      | args -> List.flatten (List.map compile_expr (args @ [expr])) @ [STA (name, List.length args)]
      )
    | Stmt.Seq (stmt1, stmt2) -> compile' stmt1 @ compile' stmt2
    | Stmt.Skip -> []
    | Stmt.If (cond, th, els) ->
      let else_label = labelGenerator#gen in
      let exit_label = labelGenerator#gen in
      (compile_expr cond) @ 
      [CJMP ("z", else_label)] @ 
      (compile' th) @ 
      [
        JMP exit_label; 
        LABEL else_label
      ] @ 
      (compile' els) @ 
      [LABEL exit_label]
    
    | Stmt.While (cond, body) ->
      let cond_label = labelGenerator#gen in
      let exit_label = labelGenerator#gen in
      [LABEL cond_label] @ 
      (compile_expr cond) @ 
      [CJMP ("z", exit_label)] @ 
      (compile' body) @ 
      [
        JMP cond_label; 
        LABEL exit_label
      ]
    | Stmt.Repeat (body, cond) ->
      let body_label = labelGenerator#gen in
      [LABEL body_label] @ 
      (compile' body) @ 
      (compile_expr cond) @ 
      [CJMP ("z", body_label)]
    | Stmt.Call (name, args) -> 
      List.concat (List.map compile_expr args) @ 
      [CALL (name, List.length args, true)]
    | Stmt.Return maybe_val -> 
      match maybe_val with 
        Some v -> (compile_expr v) @ [RET true] 
        | _ -> [RET false]

let compile_def (name, (args, local_vars, body)) = 
  [
    LABEL name; 
    BEGIN (name, args, local_vars)
  ] @ 
  (compile' body) @ 
  [END]

let rec compile (defs, program) =
  (compile' program) @ 
  [END] @ 
  (List.concat (List.map compile_def defs))
