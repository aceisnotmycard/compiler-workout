(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
       
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

    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let to_bool arg = arg <> 0

    let to_int arg = if arg then 1 else 0

    let eval_binop str x y = 
      match str with
        | "+" ->  x + y
        | "-" ->  x - y
        | "*" ->  x * y
        | "/" ->  x / y
        | "%" ->  x mod y
        | "<" ->  to_int (x < y) 
        | "<=" -> to_int (x <= y)
        | ">" ->  to_int (x > y)
        | ">=" -> to_int (x >= y)
        | "!=" -> to_int (x <> y)
        | "==" -> to_int (x == y)
        | "&&" -> to_int ((to_bool x) && (to_bool y))
        | "!!" -> to_int ((to_bool x) || (to_bool y)) 
        | _ -> failwith "Unknown operator"

    let rec eval state expr = 
      match expr with
        | Const n -> n
        | Var var -> state var
        | Binop (str, expr1, expr2) -> eval_binop str (eval state expr1) (eval state expr2)    
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
   
    *)

    let binop_mapper (operators: string list) = 
      List.map (fun op -> ostap ($(op)), fun lhs rhs -> Binop (op, lhs, rhs)) operators

    ostap (
      parse: 
        !(Ostap.Util.expr
          (fun x -> x)
          [|
            `Lefta, binop_mapper ["!!"];
            `Lefta, binop_mapper ["&&"];
            `Nona,  binop_mapper ["=="; "!="; "<="; "<"; ">="; ">"];
            `Lefta, binop_mapper ["+"; "-"];
            `Lefta, binop_mapper ["*"; "/"; "%"]
          |]
          primary
        );
      primary: 
            name: IDENT { Var name } 
          | value: DECIMAL { Const value } 
          | -"(" parse -")"
    )

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
          let new_state = Expr.update var head state in
          (new_state, tail, output)
        | Write expr -> 
          let result = Expr.eval state expr in
          (state, input, output @ [result])
        | Assign (var, expr) -> 
          let result = Expr.eval state expr in
          let new_state = Expr.update var result state in 
          (new_state, input, output)
        | Seq (stmt1, stmt2) -> 
          let cfg1 = eval (state, input, output) stmt1 in
          eval cfg1 stmt2

    (* Statement parser *)
    ostap (
      parse: seq | stmt;
      stmt: assign | read | write;
      read: -"read" -"(" var_name: IDENT -")" { Read var_name };
      write: -"write" -"(" expr: !(Expr.parse) -")" { Write expr };
      assign: var_name: IDENT -":=" expr: !(Expr.parse) { Assign(var_name, expr) };
      seq: head: stmt -";" tail: parse { Seq(head, tail) }
    )
      
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval p i =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
