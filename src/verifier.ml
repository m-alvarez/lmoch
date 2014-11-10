open Ident
open Asttypes
open Typed_ast
open Aez
open Smt

module F = Formula
module T = Term

let fresh =
  let r = ref 0 in
  let fresh () =
    r := !r + 1; "aux" ^ string_of_int !r
  in
  fresh

let declare name ?input:(input=[Type.type_int]) output =
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
  
let rec expression_to_formula time ({texpr_desc} as exp) =
  match texpr_desc with
  | TE_const (Cbool b) ->
     f_bool b, []
  | TE_ident {name} ->
     (name @@@ [time]) === (t_bool true), []
  | TE_op (Op_if, [cond; thn; els]) ->
     let cond, ec = expression_to_formula time cond in
     let f1, e1 = expression_to_formula time thn in
     let f2, e2 = expression_to_formula time els in
     (cond &&& f1) ||| ((!!cond) &&& f2), (ec @ e1 @ e2)
  | TE_op (op, exprs) when is_logic op ->
     let exprs, eqs = split @@ List.map (expression_to_formula time) exprs in
     f_operation op exprs, List.concat eqs
  | TE_op (op, exprs) when is_comparison op ->
     let exprs, eqs = split @@ List.map (expression_to_terms time) exprs in
     f_compare op (List.map List.hd exprs), List.concat eqs
  | TE_arrow (head, tail) ->
     let head, he = expression_to_formula (t_int 0) head in
     let tail, te = expression_to_formula time tail in
     (time === (t_int 0) &&& head) ||| ( (time >>> (t_int 0)) &&& tail), he @ te
  | TE_pre f ->
     let f, fe = expression_to_formula (time -- (t_int 1)) f in
     (time >>> (t_int 0)) => f, fe
  | _ ->
     Typed_ast_printer.print_exp Format.std_formatter exp;
     Format.fprintf Format.std_formatter "%!";
     failwith "failure"
and expression_to_terms time ({texpr_desc} as exp) =
  match texpr_desc with
  | TE_const (Cint i) ->
     [t_int i], []
  | TE_const (Cbool b) ->
     [t_bool b], []
  | TE_const (Creal r) ->
     failwith "We can't handle reals yet"
  | TE_ident {name} ->
     [name @@@ [time]], []
  | TE_op (Op_if, [cond; thn; els]) ->
     let cond, cnd_eq = expression_to_formula time cond in
     let thn, thn_eq = expression_to_terms time thn in
     let els, els_eq = expression_to_terms time els in
     List.map2 (ite cond) thn els, cnd_eq @ thn_eq @ els_eq 
  | TE_op (op, exprs) when is_arith op ->
     let results = List.map (expression_to_terms time) exprs in
     let exprs = List.map List.hd (List.map fst results) in
     let eqs = List.concat (List.map snd results) in
     [t_operation op exprs], eqs 
  | TE_op (op, exprs) when is_logic op ->
     let name = fresh () in
     declare name Type.type_bool;
     let formula, eqs = expression_to_formula time exp in
     [ name @@@ [time] ], ((name @@@ [time] === (t_bool true)) <=> formula) :: eqs
  | TE_op (op, [e1; e2]) when is_comparison op ->
     let name = fresh () in
     declare name Type.type_bool;
     let formula, eqs = expression_to_formula time exp in
     [name @@@ [time]], (((name @@@ [time]) === (t_bool true)) <=> formula) :: eqs
  | TE_arrow (e1, e2) ->
     let head, head_eqs = expression_to_terms (t_int 0) e1 in
     let tail, tail_eqs = expression_to_terms time e2 in
     let cond = time === (t_int 0) in
     List.map2 (ite cond) head tail, head_eqs @ tail_eqs
  | TE_pre e ->
     let terms, equations = expression_to_terms (time -- (t_int 1)) e in
     let equations = ref equations in
     List.map (fun term ->
	       let name = fresh () in
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
     let results = List.map (expression_to_terms time) exprs in
     let terms = List.concat @@ List.map fst results in
     let eqs = List.concat @@ List.map snd results in
     terms, eqs
  | TE_app ({name}, _) ->
     failwith ("What is " ^ name)
  | TE_prim ({name}, _) ->
     failwith ("What is prim " ^ name)
  | _ ->
     failwith "something went wrong"

let equation_to_formulae time {teq_patt; teq_expr} =
  let exprs, eqs = expression_to_terms time teq_expr in
  List.map2 (fun {name} expr -> name @@@ [time] === expr)
	    teq_patt.tpatt_desc
	    exprs
  @ eqs

let as_smt_type = function
  | Tbool -> Type.type_bool
  | Tint -> Type.type_int
  | Treal -> Type.type_real
	    
let declare_variables {tn_input; tn_output; tn_local; tn_equs} =
  let variables = tn_input @ tn_output @ tn_local in
  List.iter (fun ({name}, t) -> declare name (as_smt_type t)) variables
	     
	       
let node_to_formulae time {tn_equs} =
  tn_equs
  |> List.map (equation_to_formulae time)
  |> List.concat

let depth node =
  1

exception Base_case_does_not_hold
exception Inductive_case_does_not_hold

let range a b =
  let l = ref [] in
  for i = b downto a do
    l := i :: !l
  done;
  !l

let verify ({tn_input; tn_output; tn_local; tn_equs} as node) =
  try
    declare_variables node;
    let {name = variable}, _ =
      List.find (fun ({name}, _) -> String.lowercase name = "ok") tn_output
    in
    let module Base_solver = Smt.Make(struct end) in
      let depth = depth node in

      for i = 0 to depth - 1 do
	let formulae = node_to_formulae (t_int 0) node in
	List.iter (Base_solver.assume ~id:0) formulae;
      done;
      Base_solver.check ();
      List.iter
	(fun i ->
	 if not (Base_solver.entails ~id:0 ((variable @@@ [t_int i]) === T.t_true))
	 then raise Base_case_does_not_hold)
	(range 0 (depth - 1));
      print_endline "The base case holds!"
    let modul
  with
  | Base_case_does_not_hold ->
     failwith "base case does not hold"
  | Inductive_case_does_not_hold ->
     failwith "inductive case does not hold"
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
