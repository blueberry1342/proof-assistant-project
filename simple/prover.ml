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
  |Imp of ty*ty
  |Tcong of ty*ty

(** lambda-terms *)
type tm =
  |Var of var 
  |App of tm*tm
  |Abs of var*ty*tm
  |And of tm*tm

(** string representation *)
let rec string_of_ty (t:ty) : string = 
  match t with
  |Tvar(v) -> v
  |Imp(t',t'') -> "("^(string_of_ty t')^"⇒ "^(string_of_ty t'')^")"
  |Cong(t',t'') -> "("^(string_of_ty t')^"∧"^(string_of_ty t'')^")"

let () =
  assert((string_of_ty (Imp(Imp(Tvar "A",Tvar "B"),Imp(Tvar "A",Tvar "C"))))="((A⇒ B)⇒ (A⇒ C))")

let rec string_of_tm (t:tm) : string =
  match t with
  |Var(v) -> v
  |App(t',t'') -> "("^(string_of_tm t')^" "^(string_of_tm t'')^")"
  |Abs(v,ty,t') -> "(λ ("^v^" : "^(string_of_ty ty)^") -> "^(string_of_tm t')^")"
  |And(t',t'') -> "("^(string_of_tm t')^"∧"^(string_of_tm t'')^")"

let () =
  assert((string_of_tm (Abs("f",Imp(Tvar "A",Tvar "B"),Abs("x",Tvar "A",App(Var "f",Var "x")))))="(λ (f : (A⇒ B)) -> (λ (x : A) -> (f x)))")


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
        |Tvar v -> raise Type_error
        |Imp(ty,ty') -> (
          let () = check_type c t'' ty in ty'
        )
    )
    |Abs(v,ty,t') -> Imp(ty,infer_type c t')
    |And(t',t'') -> Cong(infer_type t',infer_type t'')
and check_type (c:context) (tm:tm) (ty:ty) : unit =
  if ((string_of_ty (infer_type c tm))=string_of_ty ty) then ()
    else raise Type_error



let () =
  let x = Imp(Imp(Tvar "A",Tvar "B"),Imp(Imp(Tvar "B",Tvar "C"),Imp(Tvar "A", Tvar "C"))) in
  let y = Abs("f",Imp(Tvar "A",Tvar "B"),Abs("g",Imp(Tvar "B",Tvar "C"),Abs("x",Tvar "A",App(Var "g",App(Var "f", Var "x"))))) in
  let c = [("f",Imp(Tvar "A",Tvar "B"));("g",Imp(Tvar "B",Tvar "C"));("x",Tvar "A")] in
  assert ((string_of_ty x)=(string_of_ty (infer_type c y)))

let () =
  try
    let _ = (infer_type [("f",Tvar "A")] (Abs("f",Tvar "A", Var"x"))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false

let () =
  try
    let _ = (infer_type [("f",Tvar "A");("x",Tvar "B")] (Abs("f",Tvar "A", Abs("x",Tvar "B",App(Var "f",Var "x"))))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false

let () =
  try
    let _ = (infer_type [("f",Imp(Tvar "A",Tvar "B"));("x",Tvar "B")] (Abs("f",Imp(Tvar "A",Tvar "B"), Abs("x",Tvar "B",App(Var "f",Var "x"))))) in
    assert false
  with
  | Type_error -> ()
  | _ -> assert false


let () =
  try (check_type [("x",Tvar "A")] (Abs("x",Tvar "A",Var "x")) (Imp(Tvar "A",Tvar "A"))) with
  |Type_error -> assert false

let () =
  try (check_type [("x",Tvar "A")] (Abs("x",Tvar "A",Var "x")) (Imp(Tvar "B",Tvar "B"))) with
  |Type_error -> ()
  |_ -> assert false

let () =
  try (check_type [] (Var "x") (Tvar "A")) with
  |Type_error -> ()
  |_ -> assert false


(** other connectives *)
(*????????????????????????
what to do ????????????????????????*)





