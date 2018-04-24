open GT       
open Language

(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL  of string * int * bool
(* returns from a function         *) | RET   of bool with show

(* The type for the stack machine program *)
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)
(*let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) prg = failwith "Not implemented"*)

let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn :: prg' ->
   match insn with
      | BINOP op ->
        let y::x::tail = stack in 
        eval env (cstack, (Expr.to_func op x y) :: tail, c) prg'
      | READ     -> let z::i'= i in 
        eval env (cstack, z::stack, (st, i', o)) prg'
      | WRITE    -> let z::tail = stack in 
        eval env (cstack, tail, (st, i, o @ [z])) prg'
      | CONST i  -> eval env (cstack, i::stack, c) prg'
      | LD x     -> eval env (cstack, State.eval st x :: stack, c) prg'
      | ST x     -> let z::tail = stack in 
        eval env (cstack, tail, (State.update x z st, i, o)) prg'
      | LABEL _ -> eval env conf prg'
      | JMP label -> eval env conf (env#labeled label)
      | CJMP (cond, label) -> let x :: tail = stack in
        eval env (cstack, tail, c) (if (cond = "nz" && x != 0 || cond = "z" && x = 0)
                                        then (env#labeled label) else prg')
      | BEGIN (_, args, local_vars) ->
        let current_state = State.enter st (args @ local_vars) in
        let (res_state, res_stack) = List.fold_right 
          (fun arg (st, v::tail) -> (State.update arg v st, tail)) args (current_state, stack) in
        eval env (cstack, res_stack, (res_state, i, o)) prg'
      | CALL (name, _, _) -> eval env ((prg', st)::cstack, stack, c) (env#labeled name)
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
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

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
    | Expr.Var v -> [LD v]
    | Expr.Binop (op, expr1, expr2) -> 
      (compile_expr expr1) @ 
      (compile_expr expr2) @ 
      [BINOP op]
    | Expr.Call (name, args) -> 
      List.concat (List.map compile_expr args) @ 
      [CALL (name, List.length args, false)]

let rec compile' = function
    | Stmt.Read name -> [READ;ST name]
    | Stmt.Write expr -> compile_expr expr @ [WRITE]
    | Stmt.Assign (name, expr) -> compile_expr expr @ [ST name]
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