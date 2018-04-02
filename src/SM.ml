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
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         
let rec eval env ((stack, ((st, i, output) as c)) as conf) = function
| [] -> conf
| insn::prgTail -> match insn with
      | BINOP op -> 
        let (y::x::stackTail) = stack in 
        eval env (Expr.to_func op x y::stackTail, c) prgTail

      | READ -> 
        let (z::i') = i in 
        eval env (z::stack, (st, i', output)) prgTail
      
      | WRITE -> 
        let (z::stackTail) = stack in 
        eval env (stackTail, (st, i, output @ [z])) prgTail

      | CONST i -> 
        eval env (i::stack, c) prgTail

      | LD x -> 
        eval env (st x::stack, c) prgTail

      | ST x -> 
        let (z::stackTail) = stack in 
        eval env (stackTail, (Expr.update x z st, i, output)) prgTail

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
        eval env (stackTail, c) prg 

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run program inStream =
  let module M = Map.Make (String) in
  let rec make_map map = function
  | []              -> map
  | (LABEL label)::tail -> make_map (M.add label tail map) tail
  | _::tail         -> make_map map tail
  in
  let m = make_map M.empty program in
  let env = (object method labeled l = M.find l m end) in
  let (_, (_, _, output)) = eval env ([], (Expr.empty, inStream, [])) program 
  in 
  output

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

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

let rec compile =
  let rec expr = function
  | Expr.Var x -> 
    [LD x]

  | Expr.Const n -> 
    [CONST n]

  | Expr.Binop (op, x, y) -> 
    expr x @ 
    expr y @ 
    [BINOP op]
  in
  function
  | Stmt.Seq (s1, s2) -> 
    compile s1 @ 
    compile s2

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
    compile trueBranch @ 
    [JMP endLabel] @ 
    [LABEL elseBranchLabel] @ 
    compile elseBranch @ 
    [LABEL endLabel]

  | Stmt.While (cond, body) ->
    let condLabel = labelGenerator#generateNamed "while_cond" in
    let loopLabel = labelGenerator#generateNamed "while_body" in
    let endLabel  = labelGenerator#generateNamed "while_end"  in
    [LABEL condLabel] @
    expr cond @
    [CJMP ("z", endLabel)] @
    compile body @
    [JMP condLabel] @
    [LABEL endLabel]

  | Stmt.Repeat (cond, body) ->
    let loopLabel = labelGenerator#generateNamed "repeat" in
    [LABEL loopLabel] @
    compile body @
    expr cond @
    [CJMP ("z", loopLabel)]
  
  | Stmt.Skip -> []

