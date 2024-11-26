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

(**
cat NAME.proof | dune exec ./prover.exe
*)


(** 1.3 string representation *)
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
  |Pair(t',t'') -> "("^(string_of_tm t')^","^(string_of_tm t'')^")"
  |Fst(t') -> "(fst("^(string_of_tm t')^"))"
  |Snd(t') -> "(snd("^(string_of_tm t')^"))"
  |Unit -> "()"
  |Case(t,v1,f1,v2,f2) -> "case "^(string_of_tm t)^" of "^v1^" → "^(string_of_tm f1)^" | "^v2^" → "^(string_of_tm f2)
  |Left(tm,ty) -> "left("^(string_of_tm tm)^","^(string_of_ty ty)^")"
  |Right(ty,tm) -> "left("^(string_of_ty ty)^","^(string_of_tm tm)^")"
  |Absurd(tm,ty) -> "absurd("^(string_of_tm tm)^","^(string_of_ty ty)^")"

let () =
  assert((string_of_tm (Abs("f",Imp(TVar "A",TVar "B"),Abs("x",TVar "A",App(Var "f",Var "x")))))="(λ (f : (A⇒ B)) -> (λ (x : A) -> (f x)))")


(** 1.4 typing inference*)
type context = (var * ty) list

exception Type_error


(** 1.4 and 1.5 seperated difinations of infer_type and type_checking *)
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


(** 1.6 type inference and checking together *)
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

(** 1.8 and_comm *)
let () = 
  let and_comm = Abs ("x",And(TVar "A",TVar "B"),Pair(Snd (Var "x"),Fst (Var "x"))) in
  print_endline ("and_comm : "^(string_of_ty (infer_type [] and_comm)))

(** 1.9 (⊤ ⇒ A) ⇒ A  *)
let () =
  let taa = Abs("f",Imp(True,TVar "A"),App(Var "f",Unit)) in
  print_endline ("(⊤ ⇒ A) ⇒ A : "^(string_of_ty (infer_type [] taa)))

(** 1.10 Disjunction-commutative *)
let () =
  let or_comm = Abs ("x",Or(TVar "A",TVar "B"),Case(Var "x","y",Right (TVar"B",Var "y"),"y",Left (Var "y",TVar"A"))) in
  print_endline ("or_comm : "^(string_of_ty (infer_type [] or_comm)))


(** 1.11 (A∧(A⇒⊥))⇒B *)  
let () =
  let non_contr = Abs ("x",And(TVar "A",Imp(TVar "A",False)),Absurd(App(Snd (Var "x"),Fst (Var "x")),TVar "B")) in
  print_endline ("non_contradiction : "^(string_of_ty (infer_type [] non_contr)))


 (** 1.12 Parsing strings *) 
let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l

let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)"
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
    ) l


(** 2.1 String representation of contexts *)
let rec string_of_ctx (c:context) : string = 
  match c with
    |[] -> ""
    |(var,ty)::c' when c'<>[] -> (string_of_ctx c')^" , "^var^" : "^(string_of_ty ty)
    |(var,ty)::_ -> var^" : "^(string_of_ty ty)

(** 2.2 Sequents *)
type sequent = context * ty

let string_of_seq (s:sequent) : string =
  match s with
    |(c,ty) -> (string_of_ctx c)^" |- "^(string_of_ty ty)

(**  2.3 An interactive prover *)
let rec prove file env a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove file env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | Imp (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let _ = output_string file ("\n"^cmd^" "^arg) in
            let t = prove file ((x,a)::env) b in
            Abs (x, a, t)
        |And(fst,snd) -> 
          if arg <> "" then error "Too much argument for intro." else
            let _ = output_string file ("\n"^cmd^" "^arg) in
            let t1 = prove file env fst in
            let t2 = prove file env snd in
            Pair(t1,t2)
        |True -> 
          if arg <> "" then error "Too much argument for intro." else
            let _ = output_string file ("\n"^cmd^" "^arg) in
            Unit  
       | _ ->
          error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else let _ = output_string file ("\n"^cmd^" "^arg) in t
  |"elim" -> (
      if arg = "" then error "Please provide an argument for elim." else
      let x = tm_of_string arg in
      let ty = infer_type env x in
      match ty with
        |Imp(a',b') when b'=a -> 
          let _ = output_string file ("\n"^cmd^" "^arg) in
          let t = prove file env a' in App(x,t)
        |_ -> error "Not the right type."
  )
  |"cut" -> (
    if arg = "" then error "Please provide an argument for cut." else
    let a' = ty_of_string arg in 
    let _ = output_string file ("\n"^cmd^" "^arg) in
    let t1 = prove file env (Imp(a',a)) in
    let t2 = prove file env a' in
    App(t1,t2)
  )
  |"fst" -> (
    if arg = "" then error "Please provide an argument for fst." else
    (
      let t = tm_of_string arg in 
      match infer_type env t with
        |And(a',_) when a' = a -> let _ = output_string file ("\n"^cmd^" "^arg) in (Fst t)
        |_ -> error "Not the right type."
    )
  )
  |"snd" -> (
    if arg = "" then error "Please provide an argument for snd." else
    (
      let t = tm_of_string arg in 
      match infer_type env t with
        |And(_,a') when a' = a -> let _ = output_string file ("\n"^cmd^" "^arg) in (Snd t)
        |_ -> error "Not the right type."
    )
  )
  |"left" -> (
    if arg <> "" then error "Too much argument for left." else
    match a with
      |Or(a',b') ->
        let _ = output_string file ("\n"^cmd^" "^arg) in 
        let t = prove file env a' in
        Left(t,b')
      |_ -> error "Not the right type."
  )
  |"right" -> (
    if arg <> "" then error "Too much argument for right." else
    match a with
      |Or(a',b') ->
        let _ = output_string file ("\n"^cmd^" "^arg) in 
        let t = prove file env b' in
        Right(b',t)
      |_ -> error "Not the right type."
  )
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "FILE OUTPUTING MODE : Please enter the name of the file in which you want to save the proof:";
  let b = input_line stdin in
  let file = open_out (b^".proof") in
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let _ = output_string file a in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove file [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok.";
  close_out file