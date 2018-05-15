(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

let rec init' iter n f = if iter < n 
then (f iter) :: (init' (iter + 1) n f) 
else []

(* Values *)
module Value =
  struct

    @type t = Int of int | String of string | Array of t list | Sexp of string * t list with show

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = String.init (String.length s) (fun j -> if j = i then x else s.[j])
    let update_array  a i x = init' 0 (List.length a)   (fun j -> if j = i then x else List.nth a j)

  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code s.[i]
                                     | Value.Array    a  -> List.nth a i
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"  -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Array a -> List.length a | Value.String s -> String.length s)))
    | ".array"   -> (st, i, o, Some (Value.of_array args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
    | name -> failwith name   
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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
    
    let rec eval env ((st, i, o, r) as conf) expr = match expr with
    | Const value -> (st, i, o, Some (Value.of_int value))
    | Array array -> 
      let (st, i, o, vs) = eval_list env conf array in 
      env#definition env ".array" vs (st, i, o, None)
    | String str -> (st, i, o, Some (Value.of_string str))
    | Var var -> (st, i, o, Some (State.eval st var))
    | Binop (op, l, r) -> 
      let ((st', i', o', Some l') as conf) = eval env conf l in
      let (st'', i'', o'', Some r') as conf = eval env conf r in
      (st'', i'', o'', Some (Value.of_int (to_func op (Value.to_int l') (Value.to_int r'))))
    | Elem (e, idx) -> 
      let (st, i, o, args) = eval_list env conf [e; idx] in 
      env#definition env ".elem" args (st, i, o, None)
    | Length e -> 
      let (st, i, o, Some v) = eval env conf e in 
      env#definition env ".length" [v] (st, i, o, None)
    | Call (fn, args) -> 
        let args, conf = 
          List.fold_left (fun (acc, conf) e -> let (_, _, _, Some v) as conf = eval env conf e in v::acc, conf) 
            ([], conf) args in
          env#definition env fn (List.rev args) conf
    | Sexp (tag, array) -> 
      let (st, i, o, evaluated) = eval_list env conf array in
      (st, i, o, Some (Value.Sexp (tag, evaluated)))
    and eval_list env conf xs =
      let vs, (st, i, o, _) =
        List.fold_left
          (fun (acc, conf) x ->
             let (_, _, _, Some v) as conf = eval env conf x in
             v::acc, conf
          )
          ([], conf)
          xs
      in
      (st, i, o, List.rev vs)
         
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
      
      primary: a:atom op:(-"[" idx:parse -"]" {`Elem idx} | "." %"length" {`Len})*
        {List.fold_left (fun a -> function `Elem i -> Elem (a, i) | `Len -> Length a) a op};

      atom:
          fn:IDENT -"(" args:!(Ostap.Util.list0)[parse] -")" {Call (fn, args)} 
        | c:CHAR {Const (Char.code c)}
        | s:STRING {String (String.sub s 1 (String.length s - 2))}
        | "[" elements:!(Ostap.Util.list0 parse) "]" {Array elements}
        | "`" t:IDENT args:(-"(" !(Util.list)[parse] -")")? 
          {Sexp (t, match args with None -> [] | Some ags -> ags)} 
        | n:DECIMAL {Const n}
        | x:IDENT   {Var x}
        | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "-"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl
        
        let vars p =
          transform(t) (object inherit [string list] @t[foldl] method c_Ident s _ name = name::s end) [] p
        
        (* Pattern parser *)                                 
        ostap (
          parse: 
            %"_" {Wildcard}
          | "`" t:IDENT ps:(-"(" !(Util.list)[parse] -")")? 
            {Sexp (t, match ps with None -> [] | Some ps -> ps)}
          | x: IDENT {Ident x}
        )
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update (List.nth a i) v tl))
          ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env ((st, i, o, r) as conf) k stmt = 
      let seq x = function 
        | Skip -> x
        | y -> Seq (x, y) in
      match stmt with
      | Assign (var, args, e) ->
        let (st', i', o', evals) = Expr.eval_list env conf args in
        let (st'', i'', o'', Some rv) = Expr.eval env conf e in
        eval env ((update st'' var rv evals), i'', o'', r) Skip k
      | Seq (s1, s2) -> 
        eval env conf (seq s2 k) s1
      | Skip -> (match k with 
                | Skip -> conf 
                | _ -> eval env conf Skip k) 
      | If (e, tru, fls) ->
        let (st', i', o', Some rv) = Expr.eval env conf e in
        eval env (st', i', o', r) k (if (Value.to_int rv = 0) then fls else tru) 
      | While (e, s) ->
        let (st', i', o', Some rv) = Expr.eval env conf e in
        (if (Value.to_int rv = 0)
        then eval env (st', i', o', r) Skip k
        else eval env (st', i', o', r) (seq stmt k) s)
      | Repeat (s, e) ->
        eval env conf (seq (While (Expr.Binop ("==", e, (Expr.Const 0)), s))k) s
      | Return e -> (match e with
                    | None -> (st, i, o, None)
                    | Some ret_expr -> Expr.eval env conf ret_expr)
      | Call (fn, args) -> 
        eval env (Expr.eval env conf (Expr.Call (fn, args))) k Skip
      | Case (expr, branches) -> 
        let (st', i', o', Some v) as conf' = Expr.eval env conf expr in
        let rec matchPattern pattern (value: Value.t) state = (
          match pattern, value with 
        | Pattern.Ident id, value -> Some (State.bind id value state)
        | Pattern.Wildcard, _ -> Some state
        | Pattern.Sexp (tag1, e1), Sexp (tag2, e2) when ((tag1 = tag2) && (List.length e1 = List.length e2)) ->
          List.fold_left2 (
            fun acc pat z -> (match acc with 
              None -> None 
            | Some s -> matchPattern pat z s
            )
          ) (Some state) e1 e2
        | _, _ -> None 
        ) in
        let rec checkPatterns = (function 
          | [] -> eval env conf Skip k
          | (pat, stmt)::tail -> 
            let match_res = matchPattern pat v State.undefined in (
              match match_res with 
              | None -> checkPatterns tail
              | Some s -> 
                let eval_st = State.push st' s (Pattern.vars pat) in
                eval env (eval_st, i', o', None) k (Seq (stmt, Leave))
            )
        ) in checkPatterns branches
      | Leave -> eval env (State.drop st, i, o, r) Skip k

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
        parseAssign
      | parseCall
      | parseSkip
      | parseIf
      | parseWhile
      | parseRepeat
      | parseCase
      | parseFor
      | parseReturn;

      parseAssign:
        x:IDENT index:(-"[" !(Expr.parse) -"]")* ":=" e:!(Expr.parse) 
        {Assign (x, index, e) };

      parseCall:
        funcName:IDENT "(" args: !(Expr.parse)* ")"
        { Call(funcName, args) };

      parseReturn:
        %"return" value:!(Expr.parse)? 
        { Return value };

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

      parseCase:
        %"case" e:!(Expr.parse) %"of" branches: !(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" parse)] %"esac" {Case (e, branches)};
      
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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
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
  let module M = Map.Make (String) in
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
