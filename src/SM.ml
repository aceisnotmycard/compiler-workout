open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
 let eval_insn (config: config) (insn: insn): config =
  let (stack, (state, input, output)) = config in
  match insn with
    | BINOP op -> 
      let (arg1::arg2::rest) = stack in
      let value = (Expr.eval_binop op arg2 arg1) in
      (value::rest, (state, input, output))
    | CONST value ->
      (value::stack, (state, input, output))
    | READ ->
      let (head::tail) = input in
      (head::stack, (state, tail, output))
    | WRITE -> 
      let (head::tail) = stack in
      (tail, (state, input, output @ [head]))
    | LD var ->
      let value = (state var) in
      (value::stack, (state, input, output))
    | ST var -> 
      let (head::tail) = stack in
      let new_state = Expr.update var head state in
      (tail, (new_state, input, output))
 
let rec eval (config: config) (program: prg): config = 
  match program with
    | []            -> config
    | (insn::rest)  -> 
      let new_config = eval_insn config insn in
      eval new_config rest

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
 let rec compile_expr (expr: Expr.t): prg = 
  match expr with
    | Expr.Const n           -> [CONST n]
    | Expr.Var var           -> [LD var]
    | Expr.Binop (op, a, b)  -> (compile_expr a) @ (compile_expr b) @ [BINOP op]

let rec compile (stmt: Stmt.t): prg = 
  match stmt with
    | Stmt.Read var            -> [READ] @ [ST var]
    | Stmt.Write expr          -> compile_expr expr @ [WRITE] 
    | Stmt.Assign (var, expr)  -> compile_expr expr @ [ST var]
    | Stmt.Seq (stmt1, stmt2)  -> compile stmt1 @ compile stmt2 