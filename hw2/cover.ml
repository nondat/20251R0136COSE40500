open Smt
open Utils

type sets = int * int * int list list

let sets1 : sets =
  (* 2,4,6 *)
  ( 6
  , 7
  , [ [ 1; 0; 0; 1; 0; 0; 1 ]
    ; [ 1; 0; 0; 1; 0; 0; 0 ]
    ; [ 0; 0; 0; 1; 1; 0; 1 ]
    ; [ 0; 0; 1; 0; 1; 1; 0 ]
    ; [ 0; 1; 1; 0; 0; 1; 1 ]
    ; [ 0; 1; 0; 0; 0; 0; 1 ]
    ] )
;;

type formula =
  | X of int
  | T of int * int
  | Bool of bool
  | And of formula list
  | Or of formula list
  | Not of formula
  | Imply of formula * formula
  | Iff of formula * formula
  | Neq of int * int
  
let forall f l = And (List.map f l)
let exist f l = Or (List.map f l)
(* X_i <=> s_i in S where i is row *)
(* T_ij <=> x_j in M(s_i) : in row i, col j is 1 *)
(* 1. for all col (1 <= j <= n), there exist row (1 <= i <= m) in S *)
(* 2. for all col (1 <= j <= n), for all row (1 <= i <= m - 1), not (there exist row (i + 1 <= k <= m)) *)

let encode : sets -> formula =
  fun (n, m, _) ->
  let f1 =
    forall
      (fun col -> exist (fun row -> And [ X row; T (row, col) ]) (range2 1 (n + 1)))
      (range2 1 (m + 1))
  in
  let f2 =
    forall
      (fun col ->
        forall
          (fun row_cur ->
            Not
              (exist
                 (fun row_next ->
                   And [ X row_cur; X row_next; T (row_cur, col); T (row_next, col) ])
                 (range2 (row_cur + 1) (n + 1))))
          (range2 1 n))
      (range2 1 (m + 1))
  in
  And [ f1; f2 ]
;;

let rec trans : formula -> Fmla.t list -> int list list -> Fmla.t =
  fun f s t ->
  match f with
  | X i -> List.nth s (i - 1)
  | T (row, col) -> Expr.of_bool (List.nth (List.nth t (row - 1)) (col - 1) = 1)
  | Bool b -> Expr.of_bool b
  | And fl -> Fmla.create_and (List.map (fun x -> trans x s t) fl)
  | Or fl -> Fmla.create_or (List.map (fun x -> trans x s t) fl)
  | Not _f -> Fmla.create_not (trans _f s t)
  | Imply (f1, f2) -> Fmla.create_imply (trans f1 s t) (trans f2 s t)
  | Iff (f1, f2) -> Fmla.create_iff (trans f1 s t) (trans f2 s t)
  | Neq (i1, i2) -> Expr.create_neq (Expr.of_int i1) (Expr.of_int i2)
;;

let model2lst : Model.t -> Fmla.t list -> int option list =
  fun model s ->
  List.map
    (fun i ->
      match Model.eval (List.nth s i) ~model with
      | Some expr -> if expr = Expr.true_ () then Some (i + 1) else None
      | None -> raise (Failure "model2sol"))
    (range (List.length s))
;;

let cover : sets -> int list  
=fun (n, m, t) -> ignore (n, m, t); [] (* TODO *)
