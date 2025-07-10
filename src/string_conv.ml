open EConstr
open Coqlib

let ocaml_string_of_econstr env sigma t =
  let pp = Printer.pr_econstr_env env sigma t in
  Pp.string_of_ppcmds pp

let ocaml_string_of_intropattern intropattern =
  let pp = Miscprint.pr_intro_pattern (fun _ -> Pp.str "") intropattern in
  Pp.string_of_ppcmds pp

(** Returns a Coq term of type string representing the OCaml string [s] *)
let mk_coq_string env sigma (s : string) =
  (* fetch the constructors for boolean, ascii and string based on their reference *)
  let empty_string_ref, string_cons_ref =
    (lib_ref "core.string.empty", lib_ref "core.string.string")
  in
  let ascii_cons_ref, bool_true_ref, bool_false_ref =
    ( lib_ref "core.ascii.ascii",
      lib_ref "core.bool.true",
      lib_ref "core.bool.false" )
  in
  let sigma, empty_string = Evd.fresh_global env sigma empty_string_ref in
  let sigma, string_cons = Evd.fresh_global env sigma string_cons_ref in
  let sigma, ascii_cons = Evd.fresh_global env sigma ascii_cons_ref in
  let sigma, bool_true = Evd.fresh_global env sigma bool_true_ref in
  let sigma, bool_false = Evd.fresh_global env sigma bool_false_ref in

  let mk_bool b = if b then bool_true else bool_false in

  let mk_ascii c =
    let code = Char.code c in
    let bits = List.init 8 (fun i -> code land (1 lsl i) <> 0) in
    mkApp (ascii_cons, Array.of_list (List.map mk_bool bits))
  in

  (* Build the Coq string from the OCaml string *)
  let len = String.length s in
  let rec build i acc =
    if i < 0 then acc
    else
      let char_term = mk_ascii s.[i] in
      let str_term = mkApp (string_cons, [| char_term; acc |]) in
      build (i - 1) str_term
  in
  build (len - 1) empty_string

(** Returns a Coq term of type string that represents the econstr [t] according
    to the pretty printer *)
let string_of_econstr env sigma t =
  let str = ocaml_string_of_econstr env sigma t in
  let str_term = mk_coq_string env sigma str in
  str_term

(** Returns a Coq term of type string that represents the intropattern
    [intropattern] according to the pretty printer *)
let string_of_intropattern env sigma intropattern =
  let str = ocaml_string_of_intropattern intropattern in
  let str_term = mk_coq_string env sigma str in
  str_term

(** Tactic that prints the Coq string that represents the term [t] *)
let print_string_of_term t =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let str_term = string_of_econstr env sigma t in
  let pp = Printer.pr_econstr_env env sigma str_term in
  Feedback.msg_notice pp;
  Tacticals.tclIDTAC

(** Tactic that prints the Coq string that represents the intropattern
    [intropattern] *)
let print_string_of_intropattern intropattern =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let str_term = string_of_intropattern env sigma intropattern in
  let pp = Printer.pr_econstr_env env sigma str_term in
  Feedback.msg_notice pp;
  Tacticals.tclIDTAC

(** Tactic that poses a new hypothese named [name] in the context and whose
    definition is the Coq string that represents the term [t] *)
let pose_str_term name t =
  let open Proofview in
  Goal.enter (fun gl ->
      let env = Goal.env gl in
      let sigma = Goal.sigma gl in
      let str_term = string_of_econstr env sigma t in
      let name = Names.Name.mk_name name in
      Tactics.pose_tac name str_term)

(** Tactic that poses a new hypothese named [name] in the context and whose
    definition is the Coq string that represents the intropattern [intropattern]
*)
let pose_str_intropattern name intropattern =
  let open Proofview in
  Goal.enter (fun gl ->
      let env = Goal.env gl in
      let sigma = Goal.sigma gl in
      let str_term = string_of_intropattern env sigma intropattern in
      let name = Names.Name.mk_name name in
      Tactics.pose_tac name str_term)
