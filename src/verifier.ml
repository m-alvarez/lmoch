open Ident
open Asttypes
open Typed_ast
open Aez
open Smt

module F = Formula
module T = Term

module Remember = struct
    module Int = struct
        type t = int
        let compare = Pervasives.compare
    end
    module Map = Map.Make(Int)

    let count = ref 0
    let formulae = ref Map.empty

    let reset () = begin
        count := 0;
        formulae := Map.empty
    end 

    let id_for formula = begin
        let id = !count in
        formulae := Map.add id formula !formulae;
        incr count;
        id
    end 

    let formula_of id =
        Map.find id !formulae
end 

type result = Holds | Does_not_hold of F.t

let fresh =
  let r = ref 0 in
  let fresh ?(prefix="aux") () =
    r := !r + 1; prefix ^ string_of_int !r
  in
  fresh


let declare name ?(input=[Type.type_int]) ~output =
  let name = Hstring.make name in
  if not (Symbol.declared name)
  then Symbol.declare name input output

let (@@@) name args =
  T.make_app (Hstring.make name) args

let (&&&) f1 f2 =
  F.make F.And [f1; f2]
let (|||) f1 f2 =
  F.make F.Or [f1; f2]
let (=>) f1 f2 =
  F.make F.Imp [f1; f2]
let (<=>) f1 f2 =
  (f1 => f2) &&& (f2 => f1)
let (===) t1 t2 =
  F.make_lit F.Eq [t1; t2]
let (=/=) t1 t2 =
  F.make_lit F.Neq [t1; t2]

let (--) a b =
  T.make_arith T.Minus a b

let ite f a b =
  T.make_ite f a b

let f_bool b =
  if b
  then F.f_true
  else F.f_false
				 
let t_bool b =
  if b
  then T.t_true
  else T.t_false

let t_int i =
  T.make_int (Num.num_of_int i)

let arith op =
  match op with
  | Op_add | Op_add_f -> T.Plus
  | Op_sub | Op_sub_f -> T.Minus
  | Op_mul | Op_mul_f -> T.Mult
  | Op_div | Op_div_f -> T.Div
  | Op_mod -> T.Modulo
  | _ -> failwith "not an arithmetic operator"

let is_arith op =
  try
    let _ = arith op in
    true
  with _ ->
    false

let logic op =
  match op with
  | Op_and -> F.And
  | Op_or -> F.Or
  | Op_impl -> F.Imp
  | Op_not -> F.Not
  | _ -> failwith "not a logical operation"

let is_logic op =
  try
    let _ = logic op in
    true
  with
    _ -> false

let is_comparison = function
  | Op_eq | Op_lt | Op_gt
  | Op_neq | Op_ge | Op_le -> true
  | _ -> false

let t_operation code ts = 
  match ts with
  | t :: ts ->
     let combine = T.make_arith (arith code) in
     List.fold_left combine t ts
  | _ ->
     failwith "incorrect op"
	     
let f_operation code fs =
  F.make (logic code) fs

let f_compare code fs =
  match code with
  | Op_eq -> F.make_lit F.Eq fs
  | Op_lt -> F.make_lit F.Lt fs
  | Op_le -> F.make_lit F.Le fs
  | Op_neq -> F.make_lit F.Neq fs
  | Op_gt -> F.make F.Not [F.make_lit F.Le fs]
  | Op_ge -> F.make F.Not [F.make_lit F.Lt fs]
  | _ -> failwith "not a comparison"
  
let (!!) cond =
  F.make F.Not [cond]

let (>>>) a b =
  F.make_lit F.Lt [b; a]

let split l =
  List.map fst l, List.map snd l
  
let as_smt_type = function
  | Tbool -> Type.type_bool
  | Tint -> Type.type_int
  | Treal -> Type.type_real

let declare_typed_variable ~prefix ({name}, ty) =
  let name = prefix ^ name in
  declare name (as_smt_type ty);
  name

let rec expression_to_formula nodes prefix time ({texpr_desc} as exp) =
  match texpr_desc with
  | TE_const (Cbool b) ->
     f_bool b, []
  | TE_ident {name} ->
     ((prefix ^ name) @@@ [time]) === (t_bool true), []
  | TE_op (Op_if, [cond; thn; els]) ->
     let cond, ec = expression_to_formula nodes prefix time cond in
     let f1, e1 = expression_to_formula nodes prefix time thn in
     let f2, e2 = expression_to_formula nodes prefix time els in
     (cond &&& f1) ||| ((!!cond) &&& f2), (ec @ e1 @ e2)
  | TE_op (op, exprs) when is_logic op ->
     let exprs, eqs = split @@ List.map (expression_to_formula nodes prefix time) exprs in
     f_operation op exprs, List.concat eqs
  | TE_op (op, exprs) when is_comparison op ->
     let exprs, eqs = split @@ List.map (expression_to_terms nodes prefix time) exprs in
     f_compare op (List.map List.hd exprs), List.concat eqs
  | TE_arrow (head, tail) ->
     let head, he = expression_to_formula nodes prefix (t_int 0) head in
     let tail, te = expression_to_formula nodes prefix time tail in
     (time === (t_int 0) &&& head) ||| ( (time >>> (t_int 0)) &&& tail), he @ te
  | TE_pre f ->
     let f, fe = expression_to_formula nodes prefix (time -- (t_int 1)) f in
     (time >>> (t_int 0)) => f, fe
  | _ ->
     Typed_ast_printer.print_exp Format.std_formatter exp;
     Format.fprintf Format.std_formatter "%!";
     failwith "failure"
and expression_to_terms nodes prefix time ({texpr_desc} as exp) =
  match texpr_desc with
  | TE_const (Cint i) ->
     [t_int i], []
  | TE_const (Cbool b) ->
     [t_bool b], []
  | TE_const (Creal r) ->
     failwith "We can't handle reals yet"
  | TE_ident {name} ->
     [(prefix ^ name) @@@ [time]], []
  | TE_op (Op_if, [cond; thn; els]) ->
     let cond, cnd_eq = expression_to_formula nodes prefix time cond in
     let thn, thn_eq = expression_to_terms nodes prefix time thn in
     let els, els_eq = expression_to_terms nodes prefix time els in
     List.map2 (ite cond) thn els, cnd_eq @ thn_eq @ els_eq 
  | TE_op (op, exprs) when is_arith op ->
     let results = List.map (expression_to_terms nodes prefix time) exprs in
     let exprs = List.map List.hd (List.map fst results) in
     let eqs = List.concat (List.map snd results) in
     [t_operation op exprs], eqs 
  | TE_op (op, exprs) when is_logic op ->
     let name = fresh () in
     declare name Type.type_bool;
     let formula, eqs = expression_to_formula nodes prefix time exp in
     [ name @@@ [time] ], ((name @@@ [time] === (t_bool true)) <=> formula) :: eqs
  | TE_op (op, [e1; e2]) when is_comparison op ->
     let name = fresh () in
     declare name Type.type_bool;
     let formula, eqs = expression_to_formula nodes prefix time exp in
     [name @@@ [time]], (((name @@@ [time]) === (t_bool true)) <=> formula) :: eqs
  | TE_arrow (e1, e2) ->
     let head, head_eqs = expression_to_terms nodes prefix (t_int 0) e1 in
     let tail, tail_eqs = expression_to_terms nodes prefix time e2 in
     let cond = time === (t_int 0) in
     List.map2 (ite cond) head tail, head_eqs @ tail_eqs

  | TE_pre e ->
     let terms, equations = expression_to_terms nodes prefix (time -- (t_int 1)) e in
     let equations = ref equations in
     List.map (fun term ->
	       let name = fresh ~prefix:"pre" () in
	       let typ = match term with
		 | t when Term.is_int t -> Type.type_int
		 | t when Term.is_real t -> Type.type_real
		 | t -> Type.type_bool
	       in
	       declare name typ;
	       equations := (time >>> (t_int 0) => (name @@@ [time] === term)) :: !equations;
	       name @@@ [ time ])
	      terms
     , !equations

  | TE_tuple exprs ->
     let results = List.map (expression_to_terms nodes prefix time) exprs in
     let terms = List.concat @@ List.map fst results in
     let eqs = List.concat @@ List.map snd results in
     terms, eqs

  | TE_app ({name}, args) ->
     begin
       try
	 let node = List.find (fun {tn_name={name=name'}} -> name = name') nodes in
	 let args, arg_eqs = split (List.map (expression_to_terms nodes prefix time) args) in
	 let new_prefix = fresh ~prefix:"call#" () in
	 (* We crash if one of the arguments is a tuple, just in case *)
	 let args = List.map (function [arg] -> arg | _ -> failwith "Tuple in argument position") args in
	 let arg_names =
	   List.map (fun v -> declare_typed_variable ~prefix:new_prefix v @@@ [time]) node.tn_input
	 in

	 let results =
	   List.map (fun v -> declare_typed_variable ~prefix:new_prefix v @@@ [time]) node.tn_output
	 in

	 List.iter (fun v -> ignore (declare_typed_variable ~prefix:new_prefix v); ()) node.tn_local;

	 let input_eqs = List.map2 (===) args arg_names in
	 let node_eqs = node_to_formulae nodes new_prefix time node in

	 results, input_eqs @ node_eqs
       with Not_found ->
	    failwith ("No such node " ^ name)
     end
  | TE_prim ({name}, _) ->
     failwith ("What is prim " ^ name)
  | _ ->
     failwith "something went wrong"

and equation_to_formulae nodes prefix time {teq_patt; teq_expr} =
  let exprs, eqs = expression_to_terms nodes prefix time teq_expr in
  List.map2 (fun {name} expr -> (prefix ^ name) @@@ [time] === expr)
	    teq_patt.tpatt_desc
	    exprs
  @ eqs

and node_to_formulae nodes prefix time {tn_equs} =
  tn_equs
  |> List.map (equation_to_formulae nodes prefix time)
  |> List.concat
	    
let declare_variables {tn_input; tn_output; tn_local; tn_equs} =
  let variables = tn_input @ tn_output @ tn_local in
  List.iter (fun ({name}, t) -> declare name (as_smt_type t)) variables
	     
let depth nodes node =
  1

exception Does_not_hold of Formula.t

let verify nodes ({tn_input; tn_output; tn_local; tn_equs} as node) =
  try
    declare_variables node;
    let {name = variable}, _ =
      List.find (fun ({name}, _) -> String.lowercase name = "ok") tn_output
    in
    let depth = depth nodes node in

    let report str f =
      Format.printf "%s " str;
      F.print Format.std_formatter f;
      print_newline ()
    in

    let module Base_solver = Smt.Make(struct end) in begin
	Format.printf "Asserting theory for base case\n";
	for i = 0 to depth - 1 do
	  let formulae = node_to_formulae nodes "" (t_int i) node in
	  List.iter (fun f ->
		     report "assume" f;
		     Base_solver.assume ~id:(Remember.id_for f) f)
		    formulae
	done;
	Base_solver.check ();
	
	Format.printf "Checking base case condition\n";
	for i = 0 to depth - 1 do
	  let equation = (variable @@@ [t_int i]) === T.t_true in
	  report "check" equation;
	  if not (Base_solver.entails ~id:(Remember.id_for equation) equation)
	  then raise (Does_not_hold equation)
	done;
	print_endline "The base case holds!"
    end;

    let module Inductive_solver = Smt.Make(struct end) in begin
	let n = "n" in
	declare n ~input:[] ~output:Type.type_int;

	Format.printf "Asserting theory for inductive case\n";
	for i = 0 to depth do
	  let instant = (n @@@ []) -- t_int i in
	  let formulae = node_to_formulae nodes "" instant node in
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
	    end
	done;
    try
        Inductive_solver.check ();
    with Smt.Unsat(ids) -> begin
        Format.printf "Unsatisfiable hypotheses\n";
        List.iter (fun id -> 
            F.print Format.std_formatter (Remember.formula_of id);
            print_newline ())
        ids;
        Format.printf "\n";
        let _ = read_line () in
        raise (Failure "Unsatisfiable hypotheses")
    end;

	Format.printf "Checking inductive case condition\n";
	let formula = (variable @@@ [n @@@ []] === T.t_true) in
	report "check" formula;
	if not (Inductive_solver.entails ~id:0 ((variable @@@ [n @@@ []] === T.t_true)))
	then raise (Does_not_hold formula);
	print_endline "The inductive case holds!"
    end;

    Holds
  with
  | Does_not_hold f ->
     Formula.print Format.err_formatter f;
     Format.fprintf Format.err_formatter "\n";
     Does_not_hold f
  | Smt.Error(msg) ->
     match msg with
     | DuplicateTypeName n ->
	failwith ("Duplicate type name " ^ (Hstring.view n))
     | DuplicateSymb s ->
	failwith ("Duplicate symbol " ^ (Hstring.view s))
     | UnknownType t ->
	failwith ("Unknown type " ^ (Hstring.view t))
     | UnknownSymb s ->
	failwith ("Unknown symbol " ^ (Hstring.view s))
