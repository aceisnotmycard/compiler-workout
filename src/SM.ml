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
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string with show
                                                   
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
let rec eval env ((cstack, stack, ((st, i, o) as c)) as conf) = function
| [] -> conf
| insn::prgTail -> match insn with
      | BINOP op -> 
        let (y::x::stackTail) = stack in 
        eval env (cstack, (Expr.to_func op x y)::stackTail, c) prgTail

      | READ -> 
        let (z::i') = i in 
        eval env (cstack, z::stack, (st, i', o)) prgTail
      
      | WRITE -> 
        let (z::stackTail) = stack in 
        eval env (cstack, stackTail, (st, i, o @ [z])) prgTail

      | CONST i -> 
        eval env (cstack, i::stack, c) prgTail

      | LD x -> 
        eval env (cstack, (State.eval st x)::stack, c) prgTail

      | ST x -> 
        let (z::stackTail) = stack in 
        eval env (cstack, stackTail, (State.update x z st, i, o)) prgTail

      | LABEL l -> 
        eval env conf prgTail

      | JMP label -> 
        eval env conf (env#labeled label)

      | CJMP (cond, label) ->
        let (top::stackTail) = stack in
        let prg = (if (cond = "z" && top = 0) || (cond = "nz" && top != 0) 
                  then env#labeled label
                  else prgTail)
        in
        eval env (cstack, stackTail, c) prg 
      
      | BEGIN (args, locals) -> 
        let rec init_args state = function 
          | a::args, z::stack -> 
            let state', stack' = init_args state (args, stack) in 
            State.update a z state', stack'
          | [], stack -> state, stack
        in 
        let st', stack' = init_args (State.enter st @@ args @ locals) (args, stack) in
        eval env (cstack, stack', (st', i, o)) prgTail
      
      | END ->
        (match conf with
        | (program, s)::cstack', stack, (s', i, o) ->
          eval env (cstack', stack, (State.leave s' s, i, o)) program
        | _ -> conf)
      
      | CALL f -> 
        let cstack, stack, ((s, i, o) as conf) = conf in
        eval env ((prgTail, s)::cstack, stack, conf) @@ env#labeled f

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
let labelGenerator = object
  val mutable nextLabel = 0

  method generate = 
    nextLabel <- nextLabel + 1;
    "L" ^ string_of_int nextLabel

  method generateNamed name = 
    nextLabel <- nextLabel + 1;
    name ^ "_" ^ string_of_int nextLabel
  end

let rec expr = function
  | Expr.Var x -> 
    [LD x]

  | Expr.Const n -> 
    [CONST n]

  | Expr.Binop (op, x, y) -> 
    expr x @ 
    expr y @ 
    [BINOP op]

  | Expr.Call (fn, args) ->
    List.concat (List.map expr (List.rev args)) @
    [CALL fn]

let rec compile' = function
  | Stmt.Seq (s1, s2) -> 
    compile' s1 @ 
    compile' s2

  | Stmt.Read x -> 
    [
      READ; 
      ST x
    ]

  | Stmt.Write e -> 
    expr e @ 
    [WRITE]

  | Stmt.Assign (x, e) -> 
    expr e @ 
    [ST x]

  | Stmt.If (cond, trueBranch, elseBranch) -> 
    let endLabel = labelGenerator#generateNamed "if_end" in
    let elseBranchLabel = labelGenerator#generateNamed "else" in
    expr cond @ 
    [CJMP ("z", elseBranchLabel)] @ 
    compile' trueBranch @ 
    [JMP endLabel] @ 
    [LABEL elseBranchLabel] @ 
    compile' elseBranch @ 
    [LABEL endLabel]

  | Stmt.While (cond, body) ->
    let condLabel = labelGenerator#generateNamed "while_cond" in
    let loopLabel = labelGenerator#generateNamed "while_body" in
    let endLabel  = labelGenerator#generateNamed "while_end"  in
    [LABEL condLabel] @
    expr cond @
    [CJMP ("z", endLabel)] @
    compile' body @
    [JMP condLabel] @
    [LABEL endLabel]

  | Stmt.Repeat (body, cond) ->
    let loopLabel = labelGenerator#generateNamed "repeat" in
    [LABEL loopLabel] @
    compile' body @
    expr cond @
    [CJMP ("z", loopLabel)]
  
  | Stmt.Skip -> []

  | Stmt.Return option -> 
    (match option with
    | Some e -> (expr e) @ [END]
    | _ -> [END])

  | Stmt.Call (fname, args) -> 
    List.concat (List.map expr (List.rev args)) @
    [CALL fname]


let compile_function (name, (args, locals, body)) = 
  let compiled = compile' body in
  [LABEL name] @
  [BEGIN (args, locals)] @
  compiled @
  [END]

let compile (defs, p) = 
  let main = compile' p in
  let funcs = List.fold_left 
    (fun lst def -> let c = compile_function def in c :: lst) [] defs in
  [LABEL "name"] @
  main @
  [END] @
  (List.concat funcs)