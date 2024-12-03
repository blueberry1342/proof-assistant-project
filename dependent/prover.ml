let () = Printexc.record_backtrace true

open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

(** 
dune exec ./prover.exe
cat NAME.proof | dune exec ./prover.exe
define pred = fun (n : Nat) -> Ind (fun (n : Nat) -> Nat) Z (fun (n : Nat) -> (fun (m : Nat) -> n)) n
*)

(** 5.2 String representation *)
let rec to_string (e:expr) : string =
  match e with
  |Type -> "Type"
  |Var v -> v
  |App(e1,e2) -> "("^(to_string e1)^" "^(to_string e2)^")" 
  |Abs(v,e1,e2) -> "(fun ("^v^" : "^(to_string e1)^") -> "^(to_string e2)^")"
  |Pi(x,a,b) -> "(("^x^" : "^(to_string a)^") -> "^(to_string b)^")"
  |Nat -> "Nat"
  |Z -> "Z"
  |S n -> "(S "^to_string n^")"
  |Ind(p,z,s,n) -> "Ind "^(to_string p)^" "^(to_string z)^" "^(to_string s)^" "^(to_string n)
  |Eq(t,u) -> (to_string t)^" = "^(to_string u)
  |Refl x -> "Refl "^(to_string x)
  |J(p,r,x,y,e) -> "J "^(to_string p)^" "^(to_string r)^" "^(to_string x)^" "^(to_string y)^" "^(to_string e)


(** 5.3 Fresh variable names *)
let n = ref 0

let fresh_var () : var =
  let s = !n in (
    n := !n+1;
    "x"^(string_of_int s)
    )


(**
let rec has_fv (v:var) (t:expr) :bool =
  match t with
    |Var(v') -> if (v=v') then true else false
    |App(t1,t2) -> (has_fv v t1)||(has_fv v t2)
    |Abs(v',_,t') -> if (v=v') then false else (has_fv v t')
    |Type -> false
    |Pi(v',_,b) -> if (v=v') then false else (has_fv v b)
    |_ -> assert false
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
*)


(** 5.4 Substitution *)
let rec subst (v:var) (e1:expr) (e2:expr) = 
  match e2 with
    |Type -> Type 
    |Var v' -> if v = v' then e1 else e2
    |App(a,b) -> App(subst v e1 a, subst v e1 b)
    |Abs(v',a,b) -> 
      if v'=v then e2
      else (
          let v'' = fresh_var() in
          Abs(v'',subst v e1 a,subst v e1 (subst v' (Var(v'')) b))
      )
    |Pi(v',a,b) -> 
      if v'=v then e2
      else (
          let v'' = fresh_var() in
          Pi(v'',subst v e1 a,subst v e1 (subst v' (Var(v'')) b))
      ) 
    |Nat -> Nat
    |Z -> Z
    |S n -> S (subst v e1 n)
    |Ind(p,z,s,n) -> Ind(subst v e1 p,subst v e1 z,subst v e1 s,subst v e1 n)
    |Eq(u,t) -> Eq(subst v e1 u,subst v e1 t)
    |Refl t -> Refl (subst v e1 t)
    |J(p,r,x,y,e) -> J(subst v e1 p,subst v e1 r,subst v e1 x,subst v e1 y,subst v e1 e)
(*problem : number of fresh var*)



(** 5.5 Contexts *)

type context = (var * (expr * expr option)) list

let rec string_of_context (c:context) : string =
  match c with
    |[] -> ""
    |(var,(ty,e))::c' when c'<>[] -> (
      match e with
        |None -> (string_of_context c')^"\n"^var^" : "^(to_string ty)
        |Some e' -> (string_of_context c')^"\n"^var^" : "^(to_string ty)^"="^(to_string e')
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
    match beta_reduction c ty with
      |Some ty' -> Some (Abs(v,ty',t'))
      |None ->(
        match beta_reduction c t' with
        |Some t'' -> Some (Abs(v,ty,t''))
        |None -> None
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
   |Type -> None
   |Nat -> None
   |Z -> None
   |S n -> (
    match beta_reduction c n with
     |None -> None
     |Some m -> Some (S m)
   )
   |Ind(p,z,s,n) -> (
    match beta_reduction c n with 
      |Some n' -> Some (Ind(p,z,s,n'))
      |None -> (
        match n with
          |Z -> Some z
          |S m -> Some (App(App(s,m),Ind(p,z,s,m)))
          |_ -> None
      )
   )
   |Eq(t,u) ->(
    match beta_reduction c t with
      |Some t' -> Some (Eq(t',u))
      |None -> (
        match beta_reduction c u with
          |Some u' -> Some (Eq(t,u'))
          |None -> None
      )
   )
   |Refl e -> (
    match beta_reduction c e with
      |Some e' -> Some (Refl e')
      |None -> None
   )
   |J(p,r,x,y,e) -> Some (App(App(App(App(p,r),x),y),e))

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
    |Nat -> (
      match e2 with
        |Nat -> true
        |_ -> false
    )
    |Z -> (
      match e2 with
        |Z -> true
        |_ -> false
    )
    |S n -> (
      match e2 with
        |S m -> alpha m n
        |_ -> false
    )
    |Ind(p,z,s,n) -> (
      match e2 with
        |Ind(p',z',s',n') -> (alpha p p')&&(alpha z z')&&(alpha s s')&&(alpha n n')
        |_ -> false
    )
    |Eq(t,u) -> (
      match e2 with 
        |Eq(t',u') -> (alpha t t')&&(alpha u u')
        |_ -> false
    )
    |Refl e -> (
      match e2 with
        |Refl e' -> alpha e e'
        |_ -> false
    )
    |J(p,r,x,y,e) ->(
      match e2 with 
        |J(p',r',x',y',e') -> (alpha p p')&&(alpha r r')&&(alpha x x')&&(alpha y y')&&(alpha e e')
        |_ -> false
    )


(** 5.8 Conversion *)
let conv (c:context) (e1:expr) (e2:expr) : bool =
  alpha (normalize c e1) (normalize c e2)

(** 5.9 Type inference *)
exception Type_error of string


(**
e' : (id ((_ : Bool) -> Bool)) = app id ...
infer e' 

*)


(** define pred = fun (n : Nat) -> Ind (fun (n : Nat) -> Nat) Z (fun (n : Nat) -> (fun (m : Nat) -> m)) *)

let rec infer (c:context) (e:expr) : expr =
  match e with
    |Var v -> (
      match List.assoc_opt v c with
        |None -> raise (Type_error ("Type of variable "^v^" not found."))
        |Some (ty,_)-> normalize c ty
    )
    |Abs(v,ty,e') -> normalize c (Pi(v,ty,infer ((v,(ty,None))::c) e'))
    |App(e',e'') -> (
      match (infer c e') with
        |Pi(v,a,b) -> (
          match (infer c e'') with
            |ty when (conv c ty a) -> normalize c (subst v e'' b)
            |_ -> raise (Type_error "Can not do such an application, because the second term has the wrong type.")
        )
        |_ -> raise (Type_error "Can not do such an application because the first term isn't a function.")
    )
    |Pi(_,_,_) -> Type
    |Type -> Type
    |Nat -> Type
    |Z -> Nat
    |S n -> if conv c (infer c n) Nat then Nat else raise (Type_error "Succesor doesn't make sense.")
    |Ind(p,z,s,n) -> (
      let ty1 = infer c z in 
      let ty2 = infer c s in
      let ty3 = App(p,Z) in
      if conv c ty1 ty3 then
        match ty2 with
          |Pi(v,a,b) when conv c a Nat -> 
            if conv ((v,(Nat,None))::c) b (Pi("",App(p,Var v),App(p,(S (Var v))))) then normalize c (App(p,n)) 
            else raise (Type_error ("Type of the result of s : "^(to_string (normalize c b))^" doesn't match with "^(to_string (normalize c (Pi("",App(p,Var v),App(p,(S (Var v)))))))))
          |_ -> raise  (Type_error "induction function 2")
      else  raise (Type_error ("Type of the init condition : "^(to_string (normalize c ty1))^" doesn't match with "^(to_string (normalize c ty3))))
    )
    |Eq(_,_) -> Type
    |Refl t -> Eq(t,t)
    |J(p,r,x,y,e) ->
      let a = (infer c x) in
      let b = (infer c y) in
      if conv c a b then 
        if conv c (infer c p) (Pi("x",a,Pi("y",a,Pi("",Eq(Var "x",Var "y"),Type)))) then
          if conv c (infer c r) (Pi("x",a,App(App(App(p,Var "x"),Var "x"),Refl (Var "x")))) then
            if conv c (infer c e) (Eq(x,y)) then
              normalize c (App(App(App(p,x),y),e))
            else raise (Type_error ((to_string e)^" : "^(to_string (infer c e))^" doesn't have the right type "^(to_string (normalize c (Eq(x,y))))))
          else raise (Type_error ((to_string r)^" : "^(to_string (infer c r))^" doesn't have the right type "^(to_string (normalize c (Pi("x",a,App(App(App(p,Var "x"),Var "x"),Refl (Var "x"))))))))
        else raise (Type_error ((to_string p)^" : "^(to_string (infer c p))^" doesn't have the right type "^(to_string (normalize c (Pi("x",a,Pi("y",a,Pi("",Eq(x,y),Type))))))))
      else raise (Type_error ("x : "^(to_string x)^" and y : "^(to_string y)^" don't have the same type "^(to_string (normalize c (Pi("x",a,Pi("y",a,Pi("",Eq(Var "x",Var "y"),Type))))))))

(** 5.10 Type checking *)
let check (c:context) (e:expr) (ty:expr) : unit =
  if conv c ty (infer c e) then () else raise (Type_error "Term does not have the given type")

(** 5.11 Interaction loop *)
let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "dnat.proof" in
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

(**
define pred = fun (n : Nat) -> Ind (fun (n : Nat) -> Nat) Z (fun (n : Nat) -> (fun (m : Nat) -> n)) n
eval pred Z
eval pred (S (S (S Z)))
define add = fun (n : Nat) -> fun (m : Nat) -> Ind (fun (n : Nat) -> Nat) m (fun (n : Nat) -> fun (m : Nat) -> S m) n
eval add (S (S (S Z))) (S (S Z))
*)
(*
define Seq = fun (x : Nat) -> fun (y : Nat) -> fun (e : x = y) -> J (fun (x : Nat) -> fun (y : Nat) -> fun (z : x = y) -> S x = S y) (fun (x : Nat) -> Refl (S x)) x y e
define addz = fun (n : Nat) -> Ind (fun (m : Nat) -> (add m Z = m)) (Refl Z) (fun (m : Nat) -> fun (e : add m Z = m) -> Seq (add m Z) m e) n
define zadd = fun (n : Nat) -> Refl n
define addasso = fun (n : Nat) -> fun (m : Nat) -> fun (p : Nat) -> Ind (fun (n : Nat) -> add (add n m) p = add n (add m p)) (Refl (add m p)) (fun (n : Nat) -> fun (e : add (add n m) p = add n (add m p)) -> Seq (add (add n m) p) (add n (add m p)) e) n
check addasso = Pi (n : Nat) -> Pi (m : Nat) -> Pi (p : Nat) -> add (add n m) p = add n (add m p)
define addcomm = fun (n : Nat) -> fun (m : Nat) -> Ind (fun (k : Nat) -> add m k = add k m) (addz m) (fun (l : Nat) -> fun (e : add m l = add l m) -> J (fun (x : Nat) -> fun (y : Nat) -> fun (e : x = y)) () ) n
Seq (add m l) (add l m) e    

((e : Ind (fun (x691 : Nat) -> Nat) n (fun (x688 : Nat) -> (fun (x690 : Nat) -> (S x690))) m = Ind (fun (x717 : Nat) -> Nat) m (fun (x714 : Nat) -> (fun (x716 : Nat) -> (S x716))) n) -> (S Ind (fun (x695 : Nat) -> Nat) n (fun (x692 : Nat) -> (fun (x694 : Nat) -> (S x694))) m) = (S Ind (fun (x721 : Nat) -> Nat) m (fun (x718 : Nat) -> (fun (x720 : Nat) -> (S x720))) n)) doesn't match with 
(( : Ind (fun (x854 : Nat) -> Nat) n (fun (x851 : Nat) -> (fun (x853 : Nat) -> (S x853))) m = Ind (fun (x880 : Nat) -> Nat) m (fun (x877 : Nat) -> (fun (x879 : Nat) -> (S x879))) n) -> Ind (fun (x858 : Nat) -> Nat) (S n) (fun (x855 : Nat) -> (fun (x857 : Nat) -> (S x857))) m = (S Ind (fun (x884 : Nat) -> Nat) m (fun (x881 : Nat) -> (fun (x883 : Nat) -> (S x883))) n)).

(( : Ind (fun ( : Nat) -> Nat) l (fun ( : Nat) -> (fun ( : Nat) -> (S x))) m = Ind (fun (x1005 : Nat) -> Nat) m (fun ( : Nat) -> (fun ( : Nat) -> (S x))) l) -> (S Ind (fun (x983 : Nat) -> Nat) l (fun (x980 : Nat) -> (fun (x982 : Nat) -> (S x982))) m) = (S Ind (fun (x1009 : Nat) -> Nat) m (fun (x1006 : Nat) -> (fun (x1008 : Nat) -> (S x1008))) l)) doesn't match with
(( : Ind (fun ( : Nat) -> Nat) l (fun ( : Nat) -> (fun ( : Nat) -> (S x))) m = Ind (fun (x1168 : Nat) -> Nat) m (fun ( : Nat) -> (fun ( : Nat) -> (S x))) l) -> Ind (fun (x1146 : Nat) -> Nat) (S l) (fun (x1143 : Nat) -> (fun (x1145 : Nat) -> (S x1145))) m = (S Ind (fun (x1172 : Nat) -> Nat) m (fun (x1169 : Nat) -> (fun (x1171 : Nat) -> (S x1171))) l)).
?

*) 
(*
define addsuc = fun (n : Nat) -> fun (m : Nat) -> Ind (fun (n : Nat) -> add n (S m) = add (S n) m) (Refl (S m)) (fun (n : Nat) -> fun (e : add n (S m) = add (S n) m) -> Seq (add n (S m)) (add (S n) m) e) n
define trans = fun (n : Nat) -> fun (m : Nat) -> fun (l : Nat) -> fun (e1 : n = m) -> fun (e2 : m = l) -> J 
define trans = fun (n : Nat) -> fun (m : Nat) -> fun (l : Nat) -> fun (e1 : n = m) -> fun (e2 : m = l) -> Ind (fun (n : Nat) -> n = l) (Refl Z) (fun (n : Nat) -> fun (e : n = l) -> Seq n l e) n
define trans = fun (n : Nat) -> fun (m : Nat) -> fun (l : Nat) -> fun (e1 : n = m) -> fun (e2 : m = l) -> J (fun (x : Nat) -> fun (y : Nat) -> fun (e : x = y) -> x = l) (fun (x : Nat) -> e2) n m e1
*)(** one should be much easier to define than the other ?*)

