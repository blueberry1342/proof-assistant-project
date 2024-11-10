let () = Printexc.record_backtrace true

(** ocamlopt prover.ml -o prover *) 

(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(** Types. *)
type ty =
  |Tvar of tvar
  |Imp of ty*ty

(** lambda-terms *)
type tm =
  |Var of var 
  |App of tm*tm
  |Abs of var*ty*tm

(** string representation *)
let rec string_of_ty (t:ty) : string = 
  match t with
  |Tvar(v) -> v
  |Imp(t',t'') -> "("^(string_of_ty t')^"⇒ "^(string_of_ty t'')^")"

let () =
  assert((string_of_ty (Imp(Imp(Tvar "A",Tvar "B"),Imp(Tvar "A",Tvar "C"))))="((A⇒ B)⇒ (A⇒ C))")

let rec string_of_tm (t:tm) : string =
  match t with
  |Var(v) -> v
  |App(t',t'') -> "("^(string_of_tm t')^" "^(string_of_tm t'')^")"
  |Abs(v,ty,t') -> "(λ ("^v^" : "^(string_of_ty ty)^") -> "^(string_of_tm t')^")"

let () =
  assert((string_of_tm (Abs("f",Imp(Tvar "A",Tvar "B"),Abs("x",Tvar "A",App(Var "f",Var "x")))))="(λ (f : (A⇒ B)) -> (λ (x : A) -> (f x)))")

(** typing inference*)
type context = (var * ty) list

exception Type_error

let rec infer_type (c:context) (t:tm) : ty =
  match t with
    |Var(v) -> (
      match c with
       |[] -> raise Type_error
       |(v',ty')::c' -> if v'=v then ty' else infer_type c' (Var v)
    )
    |App(t',t'') -> (
      match (infer_type c t') with
        |Tvar v -> raise Type_error
        |Imp(ty,ty') -> if ((infer_type c t'')=ty) then ty' else raise Type_error 
    )
    |Abs(v,ty,t') -> Imp(ty,infer_type c t')

let () =
  let x = Imp(Imp(Tvar "A",Tvar "B"),Imp(Imp(Tvar "B",Tvar "C"),Imp(Tvar "A", Tvar "C"))) in
  let y = Abs("f",Imp(Tvar "A",Tvar "B"),Abs("g",Imp(Tvar "B",Tvar "C"),Abs("x",Tvar "A",App(Var "g",App(Var "f", Var "x"))))) in
  let c = [("f",Imp(Tvar "A",Tvar "B"));("g",Imp(Tvar "B",Tvar "C"));("x",Tvar "A")] in
  assert ((string_of_ty x)=(string_of_ty (infer_type c y)))

let () =
  try
    let _ = (infer_type [("f",Tvar "A")] (Abs("f",Tvar "A", Var"x"))) in
    assert (false) 
  with
  | Type_error -> ()
  | _ -> assert (false) 

let () =
  try
    let _ = (infer_type [("f",Tvar "A");("x",Tvar "B")] (Abs("f",Tvar "A", Abs("x",Tvar "B",App(Var "f",Var "x"))))) in
    assert (false) 
  with
  | Type_error -> ()
  | _ -> assert (false) 

let () =
  try
    let _ = (infer_type [("f",Imp(Tvar "A",Tvar "B"));("x",Tvar "B")] (Abs("f",Imp(Tvar "A",Tvar "B"), Abs("x",Tvar "B",App(Var "f",Var "x"))))) in
    assert (false) 
  with
  | Type_error -> ()
  | _ -> assert (false) 

