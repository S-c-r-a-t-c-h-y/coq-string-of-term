open EConstr
open Coqlib

let ocaml_string_of_econstr env sigma t =
  let pp = Printer.pr_econstr_env env sigma t in
  Pp.string_of_ppcmds pp

let string_of_econstr env sigma t =
  let empty_string_ref, string_cons_ref =
    (lib_ref "core.string.empty", lib_ref "core.string.string")
  in
  let ascii_cons_ref, bool_true_ref, bool_false_ref =
    ( lib_ref "core.ascii.ascii",
      lib_ref "core.bool.true",
      lib_ref "core.bool.false" )
  in
  let str = ocaml_string_of_econstr env sigma t in
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

  let mk_coq_string (s : string) =
    let len = String.length s in
    let rec build i acc =
      if i < 0 then acc
      else
        let char_term = mk_ascii s.[i] in
        let str_term = mkApp (string_cons, [| char_term; acc |]) in
        build (i - 1) str_term
    in
    build (len - 1) empty_string
  in

  let str_term = mk_coq_string str in
  str_term

let print_string_of_term t =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let str_term = string_of_econstr env sigma t in
  let pp = Printer.pr_econstr_env env sigma str_term in
  Feedback.msg_notice pp;
  Tacticals.tclIDTAC

let pose_str name t =
  let open Proofview in
  Goal.enter (fun gl ->
      let env = Goal.env gl in
      let sigma = Goal.sigma gl in
      let str_term = string_of_econstr env sigma t in
      let name = Names.Name.mk_name name in
      Tactics.pose_tac name str_term)
