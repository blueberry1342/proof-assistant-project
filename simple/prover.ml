let () = Printexc.record_backtrace true

(** ocamlopt prover.ml -o prover
    ./prover
    git commit . -m "Implemented the proof assistant."
    git push
*) 

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  |Tvar of tvar
  |Arr of ty*ty
  |Cong of ty*ty
  |Ttrue
  |Disj of ty*ty

(** lambda-terms *)
type tm =
  |Var of var 
  |App of tm*tm
  |Abs of var*ty*tm
  |Pair of tm*tm
  |Fst of tm 
  |Snd of tm
  |True
  |Left of tm*ty
  |Right of tm*ty
  |Match of tm*tm*tm


(** string representation *)
let rec string_of_ty (t:ty) : string = 
  match t with
  |Tvar(v) -> v
  |Arr(t',t'') -> "("^(string_of_ty t')^"⇒ "^(string_of_ty t'')^")"
  |Cong(t',t'') -> "("^(string_of_ty t')^"∧"^(string_of_ty t'')^")"
  |Ttrue -> "⊤"
  |Disj(t',t'') -> "("^(string_of_ty t')^"∨"^(string_of_ty t'')^")"

let () =
  assert((string_of_ty (Arr(Arr(Tvar "A",Tvar "B"),Arr(Tvar "A",Tvar "C"))))="((A⇒ B)⇒ (A⇒ C))")

let rec string_of_tm (t:tm) : string =
  match t with
  |Var(v) -> v
  |App(t',t'') -> "("^(string_of_tm t')^" "^(string_of_tm t'')^")"
  |Abs(v,ty,t') -> "(λ ("^v^" : "^(string_of_ty ty)^") -> "^(string_of_tm t')^")"
  |Pair(t',t'') -> "("^(string_of_tm t')^"∧"^(string_of_tm t'')^")"
  |Fst(t') -> "(Fst ("^(string_of_tm t')^"))"
  |Snd(t') -> "(Snd ("^(string_of_tm t')^"))"
  |True -> "⊤"
  |Left(tm,ty) -> "(Left ("^(string_of_tm tm)^"))"
  |Right(tm,ty) -> "(Right ("^(string_of_tm tm)^"))"
  |_ -> "" (** to finish *)

let () =
  assert((string_of_tm (Abs("f",Arr(Tvar "A",Tvar "B"),Abs("x",Tvar "A",App(Var "f",Var "x")))))="(λ (f : (A⇒ B)) -> (λ (x : A) -> (f x)))")


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
        |Tvar v -> raise Type_error
        |Arr(ty,ty') -> if ((infer_type c t'')=ty) then ty' else raise Type_error 
    )
    |Abs(v,ty,t') -> Arr(ty,infer_type c t')

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
        |Arr(ty,ty') -> (
          let () = check_type c t'' ty in ty'
        )
        |_ -> raise Type_error
    )
    |Abs(v,ty,t') -> Arr(ty,infer_type ((v,ty)::c) t')
    |Pair(t',t'') -> Cong(infer_type c t',infer_type c t'')
    |Fst(t') -> (
      match (infer_type c t') with
        |Cong(ty,ty') -> ty
        |_ -> raise Type_error
    )
    |Snd(t') -> (
      match (infer_type c t') with
        |Cong(ty,ty') -> ty'
        |_ -> raise Type_error
    )
    |True -> Ttrue
    |Left(tm,ty) -> Disj(infer_type c tm,ty)
    |Right(tm,ty) -> Disj(ty,infer_type c tm)
    |Match(t',f1,f2) -> (
      match (infer_type c t') with
        |Disj(a,b) -> (
          match (infer_type c f1) with
            |Arr(a',b') when a'=a -> (
              match (infer_type c f2) with
                |Arr(a'',b'') when a''=b -> (
                  if (b'=b'') then b' else raise Type_error
                )
                |_ -> raise Type_error
            )
            |_ -> raise Type_error
        )
        |_ -> raise Type_error
    )
and check_type (c:context) (tm:tm) (ty:ty) : unit =
  if ((string_of_ty (infer_type c tm))=string_of_ty ty) then ()
    else raise Type_error



let () =
  let x = Arr(Arr(Tvar "A",Tvar "B"),Arr(Arr(Tvar "B",Tvar "C"),Arr(Tvar "A", Tvar "C"))) in
  let y = Abs("f",Arr(Tvar "A",Tvar "B"),Abs("g",Arr(Tvar "B",Tvar "C"),Abs("x",Tvar "A",App(Var "g",App(Var "f", Var "x"))))) in
  assert ((string_of_ty x)=(string_of_ty (infer_type [] y)))

let () =
  try
    let _ = (infer_type [] (Abs("f",Tvar "A", Var"x"))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false

let () =
  try
    let _ = (infer_type [] (Abs("f",Tvar "A", Abs("x",Tvar "B",App(Var "f",Var "x"))))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false

let () =
  try
    let _ = (infer_type [] (Abs("f",Arr(Tvar "A",Tvar "B"), Abs("x",Tvar "B",App(Var "f",Var "x"))))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false


let () =
  try (check_type [] (Abs("x",Tvar "A",Var "x")) (Arr(Tvar "A",Tvar "A"))) with
  |Type_error -> assert false

let () =
  try (check_type [] (Abs("x",Tvar "A",Var "x")) (Arr(Tvar "B",Tvar "B"))) with
  |Type_error -> ()
  |_ -> assert false

let () =
  try (check_type [] (Var "x") (Tvar "A")) with
  |Type_error -> ()
  |_ -> assert false



(** other connectives *)
(*????????????????????????
what to do ????????????????????????*)


let () = 
  let and_comm = Abs ("x",Cong(Tvar "A",Tvar "B"),Pair(Snd (Var "x"),Fst (Var "x"))) in
  print_endline ("and_comm : "^(string_of_ty (infer_type [] and_comm)))

(**  (⊤ ⇒ A) ⇒ A  *)
let () =
  let taa = Abs("f",Arr(Ttrue,Tvar "A"),App(Var "f",True)) in
  print_endline ("(⊤ ⇒ A) ⇒ A : "^(string_of_ty (infer_type [] taa)))

(** Disjunction-commutative *)
let () =
  let or_comm = Abs ("x",Disj(Tvar "A",Tvar "B"),Match(Var "x",Abs("y",Tvar "A",Right (Var "y",Tvar"B")),Abs("y",Tvar "B",Left (Var "y",Tvar"A")))) in
  print_endline ("or_comm : "^(string_of_ty (infer_type [] or_comm)))