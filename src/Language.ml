(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

open List
                         
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {
      g : string -> int; 
      l : string -> int; 
      scope : string list
    }

    let fail x = 
      failwith (Printf.sprintf "Undefined variable %s" x)

    (* Empty state *)
    let empty = 
      { g = fail; l = fail; scope = [] }

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s = 
      let upd f y = if x = y then v else f y in
      if List.mem x s.scope 
      then { s with l = upd s.l }
      else { s with g = upd s.g }
                                
    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = 
      (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let enter st xs = 
      { g = st.g; l = fail; scope = xs }

    (* Drops a scope *)
    let leave st st' = 
      { st with g = st'.g }

  end
    
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
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let rec eval st = function
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)     

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
          !(Ostap.Util.expr 
                  (fun x -> x)
            (Array.map (fun (a, s) -> a, 
                                List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                              ) 
                    [|                
                    `Lefta, ["!!"];
                    `Lefta, ["&&"];
                    `Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
                    `Lefta, ["+" ; "-"];
                    `Lefta, ["*" ; "/"; "%"];
                    |] 
            )
            primary);
      
      primary:
          n:DECIMAL {Const n}
        | x:IDENT   {Var x}
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
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters, local variables, and a body for given definition
    *)
     let rec eval env ((state, i, o) as conf) = function
      | Read var -> (
        match i with 
        | value::i' -> (State.update var value state, i', o) 
        | _ -> failwith "Unexpected end of input"
      )
      | Write e -> (
        state, i, o @ [Expr.eval state e]
      )
      | Assign (var, e) -> (
        State.update var (Expr.eval state e) state, i, o
      )
      | Seq (s1, s2) -> eval env (eval env conf s1) s2
      | Skip -> conf
      | If (cond, truStmt, flsStmt) -> (
        match (Expr.eval state cond) with
        | 0 -> eval env conf flsStmt
        | _ -> eval env conf truStmt  
      )
      | While  (cond, body) -> (
        let rec whileEval cond body ((st, i, o) as conf) = 
          match Expr.eval st cond with 
          | 0 -> conf
          | _ -> whileEval cond body (eval env conf body)
        in
        whileEval cond body conf
      )
      | Repeat (body, cond) -> (
        let rec repeatEval ((st, i, o) as conf) =
          match Expr.eval st cond with 
          | 0 -> repeatEval (eval env conf body)
          | _ -> conf
        in
        repeatEval (eval env conf body)
      )
      | Call (funcName, argExprs) ->
        let params, locals, body = env#definition funcName in
        let args = List.map (Expr.eval state) argExprs in
        let procScope = State.enter state (locals @ params) in 
        let updatedState = List.fold_left2 
                  (fun acc param arg -> State.update param arg acc)
                  procScope params args
        in
        let (state', i', o') = eval env (updatedState, i, o) body in
        let st' = State.leave state state' in
        (st', i', o')

    let rec parseElifChain elseStmt = function
      | (cond, body)::tail ->
        If (cond, body, parseElifChain elseStmt tail)
      | [] -> match elseStmt with 
        | None -> Skip
        | Some body -> body

    (* Statement parser *)
    ostap (
      parse:
        s:stmt ";" ss:parse {Seq (s, ss)}
      | stmt;

      stmt:
        "read" "(" x:IDENT ")"          {Read x}
      | "write" "(" e:!(Expr.parse) ")" {Write e}
      | x:IDENT ":=" e:!(Expr.parse)    {Assign (x, e)}
      | parseSkip
      | parseIf
      | parseWhile
      | parseRepeat
      | parseCall
      | parseFor;

      parseCall:
        funcName:IDENT "(" args: !(Expr.parse)* ")"
        { Call(funcName, args)};


      parseSkip:
        %"skip" 
        { Skip };

      parseIf:
        %"if" cond:!(Expr.parse)
        %"then" truStmt:parse
        elifStmts:(%"elif"!(Expr.parse) %"then" parse)*
        elseStmt:(%"else" parse)?
        %"fi"
        { If (cond, truStmt, (parseElifChain elseStmt elifStmts)) };

      parseWhile:
        %"while" cond:!(Expr.parse)
        %"do" body:parse
        %"od" 
        { While (cond, body) };

      parseRepeat:
        %"repeat" body:parse
        %"until" cond:!(Expr.parse)
        { Repeat (body, cond) };
      
      parseFor:
        %"for" init:parse "," cond:!(Expr.parse) "," upd:parse 
        %"do" body:parse
        %"od"
        { Seq (init, While (cond, Seq (body, upd))) }
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      argument:IDENT;
      parse: 
        %"fun" funcName:IDENT "(" args: !(Util.list0 argument) ")"
        locals: (%"local" !(Util.list argument))?
        "{" body: !(Stmt.parse) "}" 
        { 
          (funcName, 
          (args, 
          (match locals with 
            | None -> [] 
            | Some list -> list),
          body))
        }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i = 
  let module FuncDefs = Map.Make(String) in
  let definitions = 
    fold_left (fun m ((name, _) as def) -> FuncDefs.add name def m) FuncDefs.empty defs 
  in
  let env = 
    (object 
      method definition name = 
        snd (FuncDefs.find name definitions) 
    end) 
  in
  let _, _, o = Stmt.eval env (State.empty, i, []) body in
  o  

                                   
(* Top-level parser *)
let parse = ostap (
  defs: !(Definition.parse)*
  body: !(Stmt.parse)
  { (defs, body) }
)
