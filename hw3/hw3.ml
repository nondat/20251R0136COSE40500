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

let phi_wfp : lib list -> int -> Fmla.t =
  fun lib_lst input_n ->
  let n = List.length lib_lst + (input_n - 1) in
  (* f1 : l_I1 = 0. l_I2 = 1, ... *)
  let f1 =
    Fmla.create_and
      (List.map
         (fun i ->
           Expr.create_eq
             (Expr.create_var (Expr.sort_of_int ()) ~name:("l_I" ^ string_of_int (i + 1)))
             (Expr.of_int i))
         (range input_n))
  in
  (* f2 : l_O = N + (input_n - 1)*)
  let f2 =
    Expr.create_eq (Expr.create_var (Expr.sort_of_int ()) ~name:"l_O") (Expr.of_int n)
  in
  let f3 =
    Fmla.create_and
      (List.mapi
         (fun i (_, inputs, output, _) ->
           let l_o = Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ output) in
           (* _f1 : 0 <= l_x <= N + (input_n - 1) and l_x < l_oi for x in input *)
           let _f1 =
             Fmla.create_and
               (List.map
                  (fun x ->
                    let l_x = Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ x) in
                    Fmla.create_and
                      [ Expr.create_le (Expr.zero_ ()) l_x
                      ; Expr.create_le l_x (Expr.of_int n)
                      ; Expr.create_lt l_x l_o
                      ])
                  inputs)
           in
           (*_f2 : input_n <= l_x <= N + (input_n - 1) for x in output*)
           let _f2 =
             Fmla.create_and
               [ Expr.create_le (Expr.of_int input_n) l_o
               ; Expr.create_le l_o (Expr.of_int n)
               ]
           in
           if i = List.length lib_lst - 1
           then Fmla.create_and [ _f1; _f2 ]
           else (
             let rest = List.filteri (fun j _ -> j > i) lib_lst in
             let _f3 =
               List.fold_left
                 (fun acc (_, _, o_j, _) ->
                   let l_o_j = Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ o_j) in
                   (* let __f = Fmla.create_imply (Expr.create_neq (Expr.of_int i) (Expr.of_int (i + 1))) (Expr.create_neq l_o l_o_j) in *)
                   let __f = Expr.create_neq l_o l_o_j in
                   __f :: acc)
                 []
                 rest
             in
             Fmla.create_and [ _f1; _f2; Fmla.create_and _f3 ]))
         lib_lst)
  in
  Fmla.create_and [ f1; f2; f3 ]
;;

let rec make_new_phi : exp -> (var * var) list -> exp =
  fun e new_old ->
  let news, olds = List.split new_old in
  let old_new = List.combine olds news in
  match e with
  | INT i -> INT i
  | VAR v -> if List.mem_assoc v old_new then VAR (List.assoc v old_new) else VAR v
  | ADD (e1, e2) -> ADD (make_new_phi e1 new_old, make_new_phi e2 new_old)
  | MUL (e1, e2) -> MUL (make_new_phi e1 new_old, make_new_phi e2 new_old)
;;

let model2pgm : Model.t -> int -> lib list -> pgm =
  fun model input_n liblst ->
  let inputs = List.map (fun i -> "I" ^ string_of_int (i + 1)) (range input_n) in
  let inputs_loc_expr =
    List.map (fun v -> Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ v)) inputs
  in
  let inputs_loc =
    List.fold_right
      (fun x acc ->
        match Model.eval x ~model with
        | Some s -> int_of_string (Fmla.to_string s) :: acc
        | None -> raise (Failure "model2pgm"))
      inputs_loc_expr
      []
  in
  let inputs_loc_var = List.combine inputs_loc inputs in
  let lib_outputs_loc_var =
    List.map
      (fun (_, _, lib_output, _) ->
        let lib_output_loc_expr =
          Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ lib_output)
        in
        let lib_output_loc =
          match Model.eval lib_output_loc_expr ~model with
          | Some s -> int_of_string (Fmla.to_string s)
          | None -> raise (Failure "model2pgm")
        in
        lib_output_loc, lib_output)
      liblst
  in
  let possible_lib_inputs = List.append inputs_loc_var lib_outputs_loc_var in
  let loc_libs =
    List.map
      (fun (f_name, lib_inputs, lib_output, phi) ->
        let lib_output_loc_expr =
          Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ lib_output)
        in
        let lib_output_loc =
          match Model.eval lib_output_loc_expr ~model with
          | Some s -> int_of_string (Fmla.to_string s)
          | None -> raise (Failure "model2pgm")
        in
        let new_old_lib_inputs =
          List.map
            (fun lib_input ->
              let lib_input_loc_expr =
                Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ lib_input)
              in
              let lib_input_loc =
                match Model.eval lib_input_loc_expr ~model with
                | Some s -> int_of_string (Fmla.to_string s)
                | None -> raise (Failure "model2pgm")
              in
              let new_lib_input = List.assoc lib_input_loc possible_lib_inputs in
              new_lib_input, lib_input)
            lib_inputs
        in
        let new_lib_inputs, _ = List.split new_old_lib_inputs in
        let (EQ (e1, e2)) = phi in
        let new_phi =
          EQ (make_new_phi e1 new_old_lib_inputs, make_new_phi e2 new_old_lib_inputs)
        in
        lib_output_loc, (f_name, new_lib_inputs, lib_output, new_phi))
      liblst
  in
  let _, libs =
    List.split
      (List.sort
         (fun (l1, _) (l2, _) -> if l1 = l2 then 0 else if l1 > l2 then 1 else -1)
         loc_libs)
  in
  let _, _, output, _ = List.nth libs (List.length libs - 1) in
  inputs, libs, output
;;

let synthesize : lib list -> spec -> pgm option =
  fun lib_lst (spec_inputs, spec_output) ->
  let n = List.length spec_inputs in
  let l_i =
    List.fold_left (fun acc x -> ("I" ^ string_of_int (x + 1)) :: acc) [] (range n)
  in
  let l_I =
    List.fold_left
      (fun acc (_, inputs, _, _) ->
        List.fold_left (fun _acc input -> input :: _acc) acc inputs)
      []
      lib_lst
  in
  let l_O = List.fold_left (fun acc (_, _, output, _) -> output :: acc) [] lib_lst in
  let l_o = "O" in
  let l_conn = (l_o :: l_i) @ l_I @ l_O in
  let f_phi_wfp = phi_wfp lib_lst n in
  let f_phi_conn =
    Fmla.create_and
      (List.mapi
         (fun i x ->
           let ys = List.filteri (fun j _ -> j >= i) l_conn in
           let l_x = Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ x) in
           let vx = Expr.create_var (Expr.sort_of_int ()) ~name:x in
           Fmla.create_and
             (List.map
                (fun y ->
                  let l_y = Expr.create_var (Expr.sort_of_int ()) ~name:("l_" ^ y) in
                  let vy = Expr.create_var (Expr.sort_of_int ()) ~name:y in
                  Fmla.create_imply (Expr.create_eq l_x l_y) (Expr.create_eq vx vy))
                ys))
         l_conn)
  in
  let f_phi_lib =
    Fmla.create_and
      (List.map
         (fun (_, _, _, EQ (e1, e2)) -> Expr.create_eq (trans_exp e1) (trans_exp e2))
         lib_lst)
  in
  let f_phi_io =
    Fmla.create_and
      [ Expr.create_eq
          (Expr.create_var (Expr.sort_of_int ()) ~name:"O")
          (Expr.of_int spec_output)
      ; Fmla.create_and
          (List.mapi
             (fun i spec_input ->
               Expr.create_eq
                 (Expr.create_var
                    (Expr.sort_of_int ())
                    ~name:("I" ^ string_of_int (i + 1)))
                 (Expr.of_int spec_input))
             spec_inputs)
      ]
  in
  let f = Fmla.create_and [ f_phi_wfp; f_phi_conn; f_phi_lib; f_phi_io ] in
  let _, model_opt = Solver.check_satisfiability [ f ] in
  match model_opt with
  | Some model -> Some (model2pgm model n lib_lst)
  | None -> None
;;