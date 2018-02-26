(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

    let toBool arg = arg <> 0

    let toInt arg = if arg then 1 else 0

    let evalBinop str x y = 
      match str with
        | "+" ->  x + y
        | "-" ->  x - y
        | "*" ->  x * y
        | "/" ->  x / y
        | "%" ->  x mod y
        | "<" ->  toInt (x < y) 
        | "<=" -> toInt (x <= y)
        | ">" ->  toInt (x > y)
        | ">=" -> toInt (x >= y)
        | "!=" -> toInt (x <> y)
        | "==" -> toInt (x == y)
        | "&&" -> toInt ((toBool x) && (toBool y))
        | "!!" -> toInt ((toBool x) || (toBool y)) 
        | _ -> failwith "Unknown operator"

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval state expr = 
      match expr with
        | Const n -> n
        | Var var -> state var
        | Binop (str, expr1, expr2) -> evalBinop str (eval state expr1) (eval state expr2)

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval (state, input, output) stmt = 
      match stmt with
        | Read var -> 
          let (head::tail) = input in
          let newState = Expr.update var head state in
          (newState, tail, output)
        | Write expr -> 
          let result = Expr.eval state expr in
          (state, input, output @ [result])
        | Assign (var, expr) -> 
          let result = Expr.eval state expr in
          let newState = Expr.update var result state in 
          (newState, input, output)
        | Seq (stmt1, stmt2) -> 
          let cfg1 = eval (state, input, output) stmt1 in
          eval cfg1 stmt2
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
