open Expr

let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)

let () = Printexc.record_backtrace true

(** ocamlopt prover.ml -o prover
    ./prover
    git commit . -m "Implemented the proof assistant."
    git push
*) 

(**
dune exec ./prover.exe
make
*)


(** string representation *)
let rec string_of_ty (t:ty) : string = 
  match t with
  |TVar(v) -> v
  |Imp(t',t'') -> "("^(string_of_ty t')^"⇒ "^(string_of_ty t'')^")"
  |And(t',t'') -> "("^(string_of_ty t')^"∧"^(string_of_ty t'')^")"
  |True -> "⊤"
  |Or(t',t'') -> "("^(string_of_ty t')^"∨"^(string_of_ty t'')^")"
  |False -> "⊥ "

let () =
  assert((string_of_ty (Imp(Imp(TVar "A",TVar "B"),Imp(TVar "A",TVar "C"))))="((A⇒ B)⇒ (A⇒ C))")

let rec string_of_tm (t:tm) : string =
  match t with
  |Var(v) -> v
  |App(t',t'') -> "("^(string_of_tm t')^" "^(string_of_tm t'')^")"
  |Abs(v,ty,t') -> "(λ ("^v^" : "^(string_of_ty ty)^") -> "^(string_of_tm t')^")"
  |Pair(t',t'') -> "("^(string_of_tm t')^"∧"^(string_of_tm t'')^")"
  |Fst(t') -> "(Fst ("^(string_of_tm t')^"))"
  |Snd(t') -> "(Snd ("^(string_of_tm t')^"))"
  |Unit -> "⊤"
  |_ -> "" (** to finish *)

let () =
  assert((string_of_tm (Abs("f",Imp(TVar "A",TVar "B"),Abs("x",TVar "A",App(Var "f",Var "x")))))="(λ (f : (A⇒ B)) -> (λ (x : A) -> (f x)))")


(** typing inference*)
type context = (var * ty) list

exception Type_error


(** seperated difinations of infer_type and type_checking *)
(*
let rec infer_type (c:context) (t:tm) : ty =
  match t with
    |Var(v) -> (
      match List.assoc_opt v c with
        |None -> raise Type_error
        |Some b -> b
    )
    |App(t',t'') -> (
      match (infer_type c t') with
        |TVar v -> raise Type_error
        |Imp(ty,ty') -> if ((infer_type c t'')=ty) then ty' else raise Type_error 
    )
    |Abs(v,ty,t') -> Imp(ty,infer_type c t')

(** type checking *)
let check_type (c:context) (tm:tm) (ty:ty) : unit =
  if ((string_of_ty (infer_type c tm))=string_of_ty ty) then ()
    else raise Type_error
*)


(** type inference and checking together *)
let rec infer_type (c:context) (t:tm) : ty =
  match t with
    |Var(v) -> (
      match List.assoc_opt v c with
        |None -> raise Type_error
        |Some b -> b
    )
    |App(t',t'') -> (
      match (infer_type c t') with
        |Imp(ty,ty') -> (
          let () = check_type c t'' ty in ty'
        )
        |_ -> raise Type_error
    )
    |Abs(v,ty,t') -> Imp(ty,infer_type ((v,ty)::c) t')
    |Pair(t',t'') -> And(infer_type c t',infer_type c t'')
    |Fst(t') -> (
      match (infer_type c t') with
        |And(ty,_) -> ty
        |_ -> raise Type_error
    )
    |Snd(t') -> (
      match (infer_type c t') with
        |And(_,ty') -> ty'
        |_ -> raise Type_error
    )
    |Unit -> True
    |Left(tm,ty) -> Or(infer_type c tm,ty)
    |Right(ty,tm) -> Or(ty,infer_type c tm)
    |Case(t',v1,f1,v2,f2) -> ( (***)
      match (infer_type c t') with
        |Or(a,b) -> (
          let a' = (infer_type ((v1,a)::c) f1) in
            if ((infer_type ((v2,b)::c) f2)=a') then a'
            else raise Type_error
        )
        |_ -> raise Type_error
    )
    |Absurd(tm,ty) -> (
      match (infer_type c tm) with
        |False -> ty
        |_ -> raise Type_error
    )
and check_type (c:context) (tm:tm) (ty:ty) : unit =
  if ((string_of_ty (infer_type c tm))=string_of_ty ty) then ()
    else raise Type_error



let () =
  let x = Imp(Imp(TVar "A",TVar "B"),Imp(Imp(TVar "B",TVar "C"),Imp(TVar "A", TVar "C"))) in
  let y = Abs("f",Imp(TVar "A",TVar "B"),Abs("g",Imp(TVar "B",TVar "C"),Abs("x",TVar "A",App(Var "g",App(Var "f", Var "x"))))) in
  assert ((string_of_ty x)=(string_of_ty (infer_type [] y)))

let () =
  try
    let _ = (infer_type [] (Abs("f",TVar "A", Var"x"))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false

let () =
  try
    let _ = (infer_type [] (Abs("f",TVar "A", Abs("x",TVar "B",App(Var "f",Var "x"))))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false

let () =
  try
    let _ = (infer_type [] (Abs("f",Imp(TVar "A",TVar "B"), Abs("x",TVar "B",App(Var "f",Var "x"))))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false


let () =
  try (check_type [] (Abs("x",TVar "A",Var "x")) (Imp(TVar "A",TVar "A"))) with
  |Type_error -> assert false

let () =
  try (check_type [] (Abs("x",TVar "A",Var "x")) (Imp(TVar "B",TVar "B"))) with
  |Type_error -> ()
  |_ -> assert false

let () =
  try (check_type [] (Var "x") (TVar "A")) with
  |Type_error -> ()
  |_ -> assert false



(** other connectives *)
(*????????????????????????
what to do ????????????????????????*)


let () = 
  let and_comm = Abs ("x",And(TVar "A",TVar "B"),Pair(Snd (Var "x"),Fst (Var "x"))) in
  print_endline ("and_comm : "^(string_of_ty (infer_type [] and_comm)))

(**  (⊤ ⇒ A) ⇒ A  *)
let () =
  let taa = Abs("f",Imp(True,TVar "A"),App(Var "f",Unit)) in
  print_endline ("(⊤ ⇒ A) ⇒ A : "^(string_of_ty (infer_type [] taa)))

(** Orunction-commutative *)
let () =
  let or_comm = Abs ("x",Or(TVar "A",TVar "B"),Case(Var "x","y",Right (TVar"B",Var "y"),"y",Left (Var "y",TVar"A"))) in
  print_endline ("or_comm : "^(string_of_ty (infer_type [] or_comm)))


(** (A∧(A⇒⊥))⇒B *)  
let () =
  let non_contr = Abs ("x",And(TVar "A",Imp(TVar "A",False)),Absurd(App(Snd (Var "x"),Fst (Var "x")),TVar "B")) in
  print_endline ("non_contradiction : "^(string_of_ty (infer_type [] non_contr)))