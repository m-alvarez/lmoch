open Typed_ast
open Ident
open Aez
open Smt
open Translator
	     
exception Property_does_not_hold
exception Base_case_fails

let verify_at_depth depth nodes ({tn_input; tn_output; tn_local; tn_equs} as node) =
  try
    declare_variables node;
    let {name = variable}, _ =
      List.find (fun ({name}, _) -> String.lowercase name = "ok") tn_output
    in

    let report str f =
      Format.printf "%s " str;
      F.print Format.std_formatter f;
      print_newline ()
    in

    let module Base_solver = Smt.Make(struct end) in begin
        Format.printf "Asserting theory for base case\n";
        let f_formulae = node_to_formulae nodes "" node in
        for i = 0 to depth - 1 do
          let formulae = f_formulae (t_int i) in
          List.iter (fun f ->
                 report "assume" f;
                 Base_solver.assume ~id:(Remember.id_for f) f)
                formulae
        done;
        (try
            Base_solver.check ();
         with Smt.Unsat ids ->
             Format.eprintf "The base case contains inconsistencies\n";
             Format.eprintf "The following formulae are inconsistent:\n";
             List.iteri (fun i id ->
                 Format.eprintf "%d\t" (i + 1);
                 Formula.print Format.err_formatter (Remember.formula_of id);
                 Format.eprintf "\n";
             ) ids;
             raise Base_case_fails);
        
        Format.printf "Checking base case condition\n";
        for i = 0 to depth - 1 do
          let equation = (variable @@@ [t_int i]) === T.t_true in
          report "check" equation;
          if not (Base_solver.entails ~id:(Remember.id_for equation) equation)
          then (F.print Format.std_formatter equation; raise Base_case_fails)
        done;
        print_endline "The base case holds!"
    end;

    let module Inductive_solver = Smt.Make(struct end) in begin
        let n = fresh () in
        declare n ~input:[] ~output:Type.type_int;

        Format.printf "Asserting theory for inductive case\n";
        let f_formulae = node_to_formulae nodes "" node in
        for i = 0 to depth do
          let instant = (n @@@ []) -- t_int i in
          let formulae = f_formulae instant in
          List.iter (fun f ->
                 report "assume" f;
                 Inductive_solver.assume ~id:(Remember.id_for f) f)
                formulae;

          if i < depth 
          then Inductive_solver.assume ~id:(Remember.id_for (instant >>> t_int 0)) ( instant >>> t_int 0 );

          if i > 0
          then begin
              let equation = (variable @@@ [instant]) === T.t_true in
              Format.printf "ASSUMING INDUCTIVE HYPOTHESIS\n";
              report "assume" equation;
              Inductive_solver.assume ~id:(Remember.id_for equation) ((variable @@@ [instant]) === T.t_true);
          end;

          let t_i = fresh () in
          let t_j = fresh () in
          declare t_i ~input:[] ~output:Type.type_int;
          declare t_j ~input:[] ~output:Type.type_int;
          let left = (F.make_lit F.Lt [t_i @@@ []; t_j @@@ []]) 
              &&& (F.make_lit F.Le [t_j @@@ []; n @@@ []])
          in
          let equation =
            match
                (List.map (fun ({name=var},_) -> 
                    (var @@@ [t_i @@@ []]) =/= (var @@@ [t_j @@@ []]))
                    (tn_input @ tn_local)  )
            with
            | []  -> F.f_false
            | [e] -> left => e 
            | es  -> left => (F.make F.Or es)
          in
          Inductive_solver.assume ~id:(Remember.id_for equation) equation;
        done;
        (try
            Inductive_solver.check ();
        with Smt.Unsat(ids) -> begin
            Format.printf "Unsatisfiable hypotheses\n";
            List.iter (fun id -> 
                F.print Format.std_formatter (Remember.formula_of id);
                print_newline ())
            ids;
            Format.printf "\n";
            raise (Failure "Unsatisfiable hypotheses: this should not happen")
          end);

        Format.printf "Checking inductive case condition\n";
        let formula = (variable @@@ [n @@@ []] === T.t_true) in
        report "check" formula;
        (if not (Inductive_solver.entails ~id:0 ((variable @@@ [n @@@ []] === T.t_true)))
        then raise Property_does_not_hold);
        print_endline "The inductive case holds!"
    end;

    `Property_holds

  with
  | Property_does_not_hold ->
     `Property_does_not_hold
  | Base_case_fails ->
     `Base_case_fails

let verify ?(max_depth = 5) nodes node =
    let depth = ref 1 in
    let result = ref None in
    while !result = None do
        if !depth > max_depth
        then result := Some (`Induction_depth_exceeded max_depth)
        else match verify_at_depth !depth nodes node with
        | `Base_case_fails        -> result := Some `Property_is_false
        | `Property_holds         -> result := Some `Property_holds
        | `Property_does_not_hold -> ();
        incr depth
    done;
    match !result with
    | Some t -> t
    | None -> failwith "The impossible happened"

