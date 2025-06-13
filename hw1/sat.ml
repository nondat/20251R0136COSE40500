open Utils
(*** Do not open anything else ***)

type var = string

(*** Propositional Formulas ***)
type formula =
  | False
  | True
  | Var of var
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imply of formula * formula
  | Iff of formula * formula

let rec string_of_formula f =
  match f with
  | True -> "true"
  | False -> "false"
  | Var x -> x
  | Not f -> "(not " ^ string_of_formula f ^ ")"
  | And (f1, f2) -> "(" ^ string_of_formula f1 ^ " and " ^ string_of_formula f2 ^ ")"
  | Or (f1, f2) -> "(" ^ string_of_formula f1 ^ " or " ^ string_of_formula f2 ^ ")"
  | Imply (f1, f2) -> "(" ^ string_of_formula f1 ^ " -> " ^ string_of_formula f2 ^ ")"
  | Iff (f1, f2) -> "(" ^ string_of_formula f1 ^ " <-> " ^ string_of_formula f2 ^ ")"
;;

(*** CNF ***)
type literal = bool * var (* false means negated *)
type clause = literal list
type cnf = clause list

let string_of_literal (b, x) = if b then x else "!" ^ x

let string_of_clause c =
  string_of_list string_of_literal c ~first:"(" ~last:")" ~sep:"\\/"
;;

let string_of_cnf a = string_of_list string_of_clause a ~first:"(" ~last:")" ~sep:"/\\"

(*** DPLL ***)
exception Not_implemented
exception Rep_error

let rec compare_formula : formula -> formula -> int =
  fun f1 f2 ->
  match f1, f2 with
  | False, False | True, True -> 0
  | Var v1, Var v2 -> String.compare v1 v2
  | Not f1, Not f2 -> compare_formula f1 f2
  | And (f11, f12), And (f21, f22)
  | Or (f11, f12), Or (f21, f22)
  | Imply (f11, f12), Imply (f21, f22)
  | Iff (f11, f12), Iff (f21, f22) ->
    let c = compare_formula f11 f21 in
    if c <> 0 then c else compare_formula f12 f22
  | _, _ -> compare (key f1) (key f2)

and key : formula -> int =
  fun f ->
  match f with
  | False -> 0
  | True -> 1
  | Var _ -> 2
  | Not _ -> 3
  | And _ -> 4
  | Or _ -> 5
  | Imply _ -> 6
  | Iff _ -> 7
;;

module Formula = struct
  type t = formula

  let compare = compare_formula
end

module FormulaSet = Set.Make (Formula)

module Bool_Var = struct
  type t = bool * var

  let compare (b1, v1) (b2, v2) =
    match compare v1 v2 with
    | 0 -> compare b1 b2
    | i -> i
  ;;
end

module Bool_VarSet = Set.Make (Bool_Var)

(* Problem 1: CNF conversion *)

let rep : formula -> formula =
  fun rep_f ->
  let y = "P_" in
  match rep_f with
  | False -> False
  | True -> True
  | Var v -> Var v
  | _ -> Var (y ^ string_of_formula rep_f)
;;

let en : formula -> cnf =
  fun en_f ->
  match en_f with
  | False | True | Var _ -> []
  | Not en_f ->
    let p = rep (Not en_f) in
    let _p =
      match p with
      | Var v -> v
      | _ -> raise Rep_error
    in
    let q = rep en_f in
    (match q with
     | True -> [ [ false, _p ] ]
     | False -> [ [ true, _p ] ]
     | Var v -> [ [ false, _p; false, v ]; [ true, _p; true, v ] ]
     | _ -> raise Rep_error)
  | And (f1, f2) ->
    let p = rep en_f in
    let _p =
      match p with
      | Var v -> v
      | _ -> raise Rep_error
    in
    let q = rep f1 in
    let r = rep f2 in
    (match q, r with
     | True, True -> [ [ true, _p ] ]
     | True, False | False, True | False, False -> [ [ false, _p ] ]
     | True, Var v | Var v, True -> [ [ false, _p; true, v ]; [ false, v; true, _p ] ]
     | False, Var v | Var v, False -> [ [ false, _p ]; [ false, _p; true, v ] ]
     | Var v1, Var v2 ->
       [ [ false, _p; true, v1 ]
       ; [ false, _p; true, v2 ]
       ; [ false, v1; false, v2; true, _p ]
       ]
     | _ -> raise Rep_error)
  | Or (f1, f2) ->
    let p = rep en_f in
    let _p =
      match p with
      | Var v -> v
      | _ -> raise Rep_error
    in
    let q = rep f1 in
    let r = rep f2 in
    (match q, r with
     | True, True | True, False | False, True -> [ [ true, _p ] ]
     | False, False -> [ [ false, _p ] ]
     | True, Var v | Var v, True -> [ [ true, _p ]; [ false, v; true, _p ] ]
     | False, Var v | Var v, False -> [ [ false, _p; true, v ]; [ false, v; true, _p ] ]
     | Var v1, Var v2 ->
       [ [ false, _p; true, v1; true, v2 ]
       ; [ false, v1; true, _p ]
       ; [ false, v2; true, _p ]
       ]
     | _ -> raise Rep_error)
  | Imply (f1, f2) ->
    let p = rep en_f in
    let _p =
      match p with
      | Var v -> v
      | _ -> raise Rep_error
    in
    let q = rep f1 in
    let r = rep f2 in
    (match q, r with
     | True, True | False, True | False, False -> [ [ true, _p ] ]
     | True, False -> [ [ false, _p ] ]
     | True, Var v -> [ [ false, _p; true, v ]; [ false, v; true, _p ] ]
     | False, Var v -> [ [ true, _p ]; [ false, v; true, _p ] ]
     | Var v, True -> [ [ true, v; true, _p ]; [ true, _p ] ]
     | Var v, False -> [ [ false, _p; false, v ]; [ true, v; true, _p ]; [ true, _p ] ]
     | Var v1, Var v2 ->
       [ [ false, _p; false, v1; true, v2 ]
       ; [ true, v1; true, _p ]
       ; [ false, v2; true, _p ]
       ]
     | _ -> raise Rep_error)
  | Iff (f1, f2) ->
    let p = rep en_f in
    let _p =
      match p with
      | Var v -> v
      | _ -> raise Rep_error
    in
    let q = rep f1 in
    let r = rep f2 in
    (match q, r with
     | True, True | False, False -> [ [ true, _p ] ]
     | True, False | False, True -> [ [ false, _p ] ]
     | True, Var v | Var v, True -> [ [ false, _p; true, v ]; [ true, _p; false, v ] ]
     | False, Var v | Var v, False -> [ [ false, _p; false, v ]; [ true, _p; true, v ] ]
     | Var v1, Var v2 ->
       [ [ false, _p; false, v1; true, v2 ]
       ; [ false, _p; true, v1; false, v2 ]
       ; [ true, _p; false, v1; false, v2 ]
       ; [ true, _p; true, v1; true, v2 ]
       ]
     | _ -> raise Rep_error)
;;

let rec sub : formula -> FormulaSet.t -> FormulaSet.t =
  fun sub_f s ->
  match sub_f with
  | False | True | Var _ -> FormulaSet.add sub_f s
  | Not f ->
    let new_s = sub f s in
    FormulaSet.add sub_f new_s
  | And (f1, f2) | Or (f1, f2) | Imply (f1, f2) | Iff (f1, f2) ->
    let new_s1 = sub f1 s in
    let new_s2 = sub f2 new_s1 in
    FormulaSet.add sub_f new_s2
;;

let rec make_en_and : formula list -> cnf =
  fun l ->
  match l with
  | hd :: tl -> en hd @ make_en_and tl
  | _ -> []
;;

let convert : formula -> cnf =
  fun f ->
  let sub_F = sub f (FormulaSet.of_list []) in
  let list_sub = FormulaSet.elements sub_F in
  let rep_f = rep f in
  let en_and = make_en_and list_sub in
  let _rep_f =
    match rep_f with
    | True -> []
    | False -> [ [] ]
    | Var v -> [ [ true, v ] ]
    | _ -> raise Rep_error
  in
  _rep_f @ en_and
;;

(* Problem 2: substitution a[v/x] (replacing x by v in a) *)
let subst : cnf -> bool -> var -> cnf 
=fun a v x -> ignore (a,v,x); raise Not_implemented  (* TODO *)

(* Problem 3: boolean constraint propagation *)
let (* rec *) bcp : cnf -> cnf
=fun _ -> raise Not_implemented (* TODO *)

(* Problem 4: pure literal elimination *)
let (* rec *) ple : cnf -> cnf 
=fun _ -> raise Not_implemented (* TODO*)

let choose : cnf -> var 
=fun a -> snd (List.hd (List.hd a))

let rec dpll : cnf -> bool 
=fun a ->  
  let a = ple (bcp a) in 
    if a = [] then true  (* /\ [] = true *)
    else if List.mem [] a then false (* \/ [] = false *)
    else 
      let x = choose a in 
        dpll (subst a false x) || dpll (subst a true x) 

let solve : formula -> bool 
=fun f -> dpll (convert f)