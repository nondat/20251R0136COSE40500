open Smt
open Utils

type pgm = var list * lib list * var (* pgm = inputs, libs, output*)
and lib = var * var list * var * phi (* lib = f_name, inputs, output, phi *)
and var = string
and phi = EQ of exp * exp

and exp =
  | INT of int
  | VAR of var
  | ADD of exp * exp
  | MUL of exp * exp

type spec = int list * int

let string_of_pgm (invars, libs, outvar) =
  "def f("
  ^ string_of_list id invars ~first:"" ~last:""
  ^ "): "
  ^ "\n"
  ^ list_fold
      (fun (name, ins, out, _) s ->
        s ^ "  " ^ out ^ " := " ^ name ^ string_of_list id ins ^ "\n")
      libs
      ""
  ^ "  return "
  ^ outvar
  ^ "\n"
;;

let rec trans_exp : exp -> Fmla.t =
  fun e ->
  match e with
  | INT i -> Expr.of_int i
  | VAR v -> Expr.create_var (Expr.sort_of_int ()) ~name:v
  | ADD (e1, e2) -> Expr.create_add (trans_exp e1) (trans_exp e2)
  | MUL (e1, e2) -> Expr.create_mul (trans_exp e1) (trans_exp e2)
;;

let encode : pgm -> spec -> Fmla.t =
  fun (inputs, libs, output) (spec_inputs, spec_output) ->
  let inputs_f =
    List.map (fun x -> Expr.create_var (Expr.sort_of_int ()) ~name:x) inputs
  in
  let f1 =
    Fmla.create_and
      (List.mapi
         (fun i x -> Expr.create_eq x (Expr.of_int (List.nth spec_inputs i)))
         inputs_f)
  in
  let f2 =
    Fmla.create_and
      (List.map
         (fun (_, _, _, EQ (e1, e2)) -> Expr.create_eq (trans_exp e1) (trans_exp e2))
         libs)
  in
  let f3 =
    Expr.create_eq
      (Expr.create_var (Expr.sort_of_int ()) ~name:output)
      (Expr.of_int spec_output)
  in
  Fmla.create_and [ f1; f2; f3 ]
;;

let verify : pgm -> spec -> bool =
  fun pgm spec ->
  let f = encode pgm spec in
  let _, model_opt = Solver.check_satisfiability [ f ] in
  match model_opt with
  | Some _ -> true
  | None -> false
;;

let synthesize : lib list -> spec -> pgm option 
=fun _ _ -> None (* TODO *)