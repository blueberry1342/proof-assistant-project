let () = Printexc.record_backtrace true

open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)


(** 5.2 String representation *)
let rec to_string (e:expr) : string =
  match e with
  |Type -> "Set"
  |Var(v) -> v
  |App(e1,e2) -> "("^(to_string e1)^" "^(to_string e2)^")" 
  |Abs(v,e1,e2) -> "(λ ("^v^" : "^(to_string e1)^") -> "^(to_string e2)^")"
  |Pi(x,a,b) -> "Π ("^x^":"^(to_string a)^") -> "^(to_string b)
  |_ -> assert false


(** 5.3 Fresh variable names *)
let n = ref 0

let fresh_var () : var =
  let s = !n in (
    n := !n+1;
    "x"^(string_of_int s)
    )


(** 5.4 Substitution *)
let rec has_fv (v:var) (t:expr) :bool =
  match t with
    |Var(v') -> if (v=v') then true else false
    |App(t1,t2) -> (has_fv v t1)||(has_fv v t2)
    |Abs(v',_,t') -> if (v=v') then false else (has_fv v t')
    |Type -> assert false
    |Pi(_,_,_) -> assert false
    |_ -> assert false

(** ??? *)
let rec subst (v:var) (e1:expr) (e2:expr) = 
  match e2 with
    |Type -> Type 
    |Var v' -> if v = v' then e1 else e2
    |App(a,b) -> App(subst v e1 a, subst v e1 b)
    |Abs(v',a,b) -> 
      if v'=v then e2
      else (
        if (has_fv v' e1) then (
          let v''=fresh_var() in
          Abs(v'',subst v e1 a,subst v e1 (subst v' (Var(v'')) b))
        )
        else Abs(v',subst v e1 a,subst v e1 b)
      )
    |Pi(v',a,b) -> 
      if v'=v then e2
      else (
        if (has_fv v' e1) then (
          let v''=fresh_var() in
          Pi(v'',subst v e1 a,subst v e1 (subst v' (Var(v'')) b))
        )
        else Pi(v',subst v e1 a,subst v e1 b)
      ) 
    |_ -> assert false

(** 5.5 Contexts *)

type context = (var * (expr * expr option)) list

let rec string_of_context (c:context) : string =
  match c with
    |[] -> ""
    |(var,(ty,e))::c' when c'<>[] -> (
      match e with
        |None -> (string_of_context c')^" , "^var^" : "^(to_string ty)
        |Some e' -> (string_of_context c')^" , "^var^" : "^(to_string ty)^"="^(to_string e')
    )
    |(var,(ty,e))::_ -> (
      match e with
        |None -> var^" : "^(to_string ty)
        |Some e' -> var^" : "^(to_string ty)^"="^(to_string e')
    )
      
(** 5.6 Normalization *)

let rec find_value (c:context) (v:var) : expr option =
  match c with
    |(var,(_,e))::c' -> if var = v then e else find_value c' v
    |[] -> None

let rec beta_reduction (c:context) (t:expr) : expr option =
  match t with
   |Var(v) -> (
    match (find_value c v) with
      |None -> None
      |Some e -> (
        match beta_reduction c e with
          |None -> Some e
          |Some e' -> Some e'
      )
    )
   |Abs(v,ty,t') -> (
    match (beta_reduction c t') with
      |None -> (
        match (beta_reduction c ty) with
          |None -> None
          |Some ty' -> Some (Abs(v,ty',t'))
      )
      |Some t'' -> (
        match (beta_reduction c ty) with
          |None -> Some (Abs(v,ty,t''))
          |Some ty' -> Some (Abs(v,ty',t''))
      )
   )
   |App(t1,t2) -> (
    match t1 with
      |Abs(v,_,t3) -> Some (subst v t2 t3)
      |_ -> (
        match beta_reduction c t1 with
          |Some t1' -> Some (App(t1',t2))
          |None -> (
            match beta_reduction c t2 with
              |Some t2' -> Some (App(t1,t2'))
              |None -> None
          )
      )
   )
   |Pi(v',a,b) -> (
    match (beta_reduction c a) with
      |None -> (
        match (beta_reduction c b) with
          |None -> None
          |Some b' -> Some (Pi(v',a,b'))
      )
      |Some a' -> (
        match (beta_reduction c b) with
          |None -> Some (Abs(v',a',b))
          |Some b' -> Some (Pi(v',a',b'))
      )
   )
   |_ -> assert false

let rec normalize (c:context) (e:expr) : expr =
  match beta_reduction c e with 
    |Some e' -> normalize c e'
    |None -> e


(** 5.7 α-conversion *)

let rec alpha (e1:expr) (e2:expr) :bool =
  match e1 with
    |Var(v1)->(
      match e2 with
        |Var(v2) when v1=v2 ->true
        |_-> false
    )
    |App(e1',e1'')->(
      match e2 with
        |App(e2',e2'')->(alpha e1' e2')&&(alpha e1'' e2'')
        |_->false
    )
    |Abs(v1,ty1,e1')->(
      match e2 with
        |Abs(v2,ty2,e2') when (alpha ty1 ty2) ->
          let v3=fresh_var () in
          alpha (subst v1 (Var(v3)) e1') (subst v2 (Var(v3)) e2')
        |_->false
    )
    |Pi(v1,a1,b1) -> (
      match e2 with
        |Pi(v2,a2,b2) when (alpha a1 a2) ->
          let v3=fresh_var () in
          alpha (subst v1 (Var(v3)) b1) (subst v2 (Var(v3)) b2)
        |_ -> false
    )
    |Type -> (
      match e2 with
          |Type -> true
          |_ -> false
    )
    |_ -> assert false

(** 5.8 Conversion *)
let conv (c:context) (e1:expr) (e2:expr) : bool =
  alpha (normalize c e1) (normalize c e2)

(** 5.9 Type inference *)
exception Type_error of string

let rec infer (c:context) (e:expr) : expr =
  match e with
    |Var v -> (
      match List.assoc_opt v c with
        |None -> raise (Type_error ("Type of variable "^v^" not found."))
        |Some (ty,_)-> ty
    )
    |Abs(v,ty,e') -> Pi(v,ty,infer ((v,(ty,None))::c) e')
    |App(e',e'') -> (
      match (infer c e') with
        |Pi(v,a,b) -> (
          match (infer c e'') with
            |ty when (conv c ty a) -> subst v e' b
            |_ -> raise (Type_error "Can not do such an application, because the second term has the wrong type.")
        )
        |_ -> raise (Type_error "Can not do such an application because the first term isn't a function.")
    )
    |Pi(_,_,_) -> Type
    |Type -> Type
    |_ -> assert false

(** 5.10 Type checking *)
let check (c:context) (e:expr) (ty:expr) : unit =
  if conv c ty (infer c e) then () else raise (Type_error "Term does not have the given type")

(** 5.11 Interaction loop *)
let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
        let x, sa = split ':' arg in
        let a = of_string sa in
        check !env a Type;
        env := (x,(a,None)) :: !env;
        print_endline (x^" assumed of type "^to_string a)
      | "define" ->
        let x, st = split '=' arg in
        let t = of_string st in
        let a = infer !env t in
        env := (x,(a,Some t)) :: !env;
        print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
        print_endline (string_of_context !env)
      | "type" ->
        let t = of_string arg in
        let a = infer !env t in
        print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
        let t, a = split '=' arg in
        let t = of_string t in
        let a = of_string a in
        check !env t a;
        print_endline "Ok."
      | "eval" ->
        let t = of_string arg in
        let _ = infer !env t in
        print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | Type_error err -> print_endline ("Typing error :"^err^".")
    | Parsing.Parse_error -> print_endline ("Parsing error.")
  done;
  print_endline "Bye." 