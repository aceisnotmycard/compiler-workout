open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
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
| insn :: prg' -> (match insn with
  | BINOP op -> let y::x::stack' = stack in eval env (cstack, (Value.of_int @@ Expr.to_func op (Value.to_int x) (Value.to_int y)) :: stack', c) prg'
  | CONST i  -> eval env (cstack, (Value.of_int i)::stack, c) prg'
  | STRING s -> eval env (cstack, (Value.of_string s)::stack, c) prg'
  | SEXP (tag, count) -> let exprs, rest = split count stack in eval env (cstack, (Value.sexp tag (List.rev exprs)) :: rest, c) prg'
  | LD x     -> eval env (cstack, (State.eval st x) :: stack, c) prg'
  | ST x     -> let z::stack'    = stack in eval env (cstack, stack', (State.update x z st, i, o)) prg'
  | STA (x, n) -> 
    let v::ind, stack' = split (n + 1) stack in 
    eval env (cstack, stack', (Language.Stmt.update st x v (List.rev ind), i, o)) prg'
  | LABEL _  -> eval env conf prg'
  | JMP l    -> eval env conf (env#labeled l)
  | CJMP (cond, l) ->
    let z::stack' = stack in
    let is_jump = match cond with
    | "nz" -> Value.to_int z <> 0
    | "z" -> Value.to_int z == 0
    in eval env (cstack, stack', c) (if is_jump then (env#labeled l) else prg')
  | BEGIN (_, args, local_vars) ->
    let init_val = fun x ((v :: stack), st) -> (stack, State.update x v st) in
    let (stack', st') = List.fold_right init_val args (stack, State.enter st (args @ local_vars)) in
    eval env (cstack, stack', (st', i, o)) prg'
  | CALL (fn, n, p) -> (
    if env#is_label fn
    then eval env ((prg', st)::cstack, stack, c) (env#labeled fn) 
    else eval env (env#builtin conf fn n p) prg'
    )
  | DROP -> eval env (cstack, List.tl stack, c) prg'
  | DUP -> let hd::_ = stack in eval env (cstack, hd::stack, c) prg'
  | SWAP -> let x::y::rest = stack in eval env (cstack, y::x::rest, c) prg'
  | TAG s -> 
    let sexp::tl = stack in 
    let res = if s = Value.tag_of sexp then 1 else 0 in 
    eval env (cstack, (Value.of_int res)::tl, c) prg'
  | ENTER es -> 
    let vals, rest = split (List.length es) stack in
    let st' = List.fold_left2 (fun acc e var -> State.bind var e acc) State.undefined vals es in 
    eval env (cstack, rest, (State.push st st' es, i, o)) prg'
  | LEAVE -> eval env (cstack, stack, (State.drop st, i, o)) prg'
  | END | RET _ -> (match cstack with
    | (p, stt)::cstack' -> eval env (cstack', stack, (State.leave st stt, i, o)) p
    | [] -> conf
    )
  )


(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
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
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (label f, List.length args, p)]
  and pattern lfalse pat = (
    let rec comp = function
    | Stmt.Pattern.Wildcard -> [DROP]
    | Stmt.Pattern.Ident _ -> [DROP]
    | Stmt.Pattern.Sexp (tag, exprs) -> (
      let res, _ = List.fold_left 
        (fun (acc, pos) p -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ comp p, pos + 1)) 
        ([], 0) exprs in
      [DUP; TAG tag; CJMP ("z", lfalse)] @ res
    ) in comp pat
  ) 
  and bindings p = (
    let rec bind = (function
       | Stmt.Pattern.Wildcard -> [DROP]
       | Stmt.Pattern.Ident _ -> [SWAP]
       | Stmt.Pattern.Sexp (_, xs) ->
         let res, _ = List.fold_left 
          (fun (acc, pos) p -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind p, pos + 1)) 
          ([], 0) xs 
         in res @ [DROP]
     ) in bind p @ [ENTER (Stmt.Pattern.vars p)]
  )
  and expr = (function
    | Expr.Var x -> 
      [LD x]
    | Expr.Const n -> 
      [CONST n]
    | Expr.String s -> 
      [STRING s]
    | Expr.Binop (op, x, y) -> 
      (expr x) @ (expr y) @ [BINOP op]
    | Expr.Call (fn, args) -> 
      call fn args false
    | Expr.Array xs -> 
      call ".array" xs false 
    | Expr.Elem (array, idx) -> 
      call ".elem" [array; idx] false
    | Expr.Length e -> 
      call ".length" [e] false
    | Expr.Sexp (tag, exprs) -> 
      let compiled = List.fold_left (fun acc ex -> acc @ (expr ex)) [] exprs in 
      compiled @ [SEXP (tag, List.length exprs)]
  ) in
  let rec compile_stmt l env = (function
    | Stmt.Seq (s1, s2)  -> 
      let env, _, c1 = compile_stmt l env s1 in
      let env, _, c2 = compile_stmt l env s2 in
      env, false, c1 @ c2
    | Stmt.Assign (x, [], e) -> 
      env, false, (expr e) @ [ST x]
    | Stmt.Assign (x, idxs, e) -> 
      env, false, List.flatten (List.map expr (idxs @ [e])) @ [STA (x, List.length idxs)]
    | Stmt.Skip -> 
      env, false, []
    | Stmt.If (cond, tru, fls) -> (
      let else_label, env = env#get_label in 
      let end_label, env = env#get_label in
      let env, _, tru_comp = compile_stmt l env tru in
      let env, _, fls_comp = compile_stmt l env fls in
      env, false, (expr cond @ [CJMP ("z", else_label)] @ tru_comp @ [JMP end_label] @ [LABEL else_label] @ fls_comp @ [LABEL end_label])
    )
    | Stmt.Repeat (stmt, cond) -> (
      let repeat_body_label, env = env#get_label in
      let env, _, comp = compile_stmt l env stmt in
      env, false, ([LABEL repeat_body_label] @ comp @ expr cond @ [CJMP ("z", repeat_body_label)])
    )
    | Stmt.While (cond, stmt) -> (
      let while_body_label, env = env#get_label in
      let end_label, env = env#get_label in
      let env, _, comp = compile_stmt l env stmt in
      env, false, ([JMP end_label] @ [LABEL while_body_label] @ comp @ [LABEL end_label] @ expr cond @ [CJMP ("nz", while_body_label)])
    )
    | Stmt.Call (fn, args) -> 
      env, false, call fn args true
    | Stmt.Case (ex, patts) -> 
      let rec compilePattern env lbl fst lend = (function
        | [] -> env, []
        | (p, act)::tail -> 
          let env, _, body = compile_stmt l env act in 
          let lfalse, env = env#get_label
          and start = if fst then [] else [LABEL lbl] in
          let env, code = compilePattern env lfalse false lend tail in
          env, start @ (pattern lfalse p) @ bindings p @ body @ [LEAVE; JMP lend] @ code
        ) in
      let lend, env = env#get_label in
      let env, code = compilePattern env "" true lend patts in
      env, false, expr ex @ code @ [LABEL lend]
    | Stmt.Leave -> 
      env, false, [LEAVE]
    | Stmt.Return m_v -> 
      env, false, (match m_v with 
      None -> []
      | Some v -> (expr v)) 
      @ [RET (m_v <> None)]
  ) in
  let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code) 

