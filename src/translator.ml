open Ident
open Asttypes
open Typed_ast
open Aez
open Smt

module F = Formula
module T = Term

module Remember : sig
    val id_for : F.t -> int
    val formula_of : int -> F.t
end = struct
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

let fresh =
  let r = ref 0 in
  let fresh ?(prefix="aux") () =
    r := !r + 1; prefix ^ string_of_int !r
  in
  fresh

let declare name ?(input=[Type.type_int]) ~output =
  let name = Hstring.make name in
  (* Unfortunately this causes rubbish to be printed to stderr *)
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

let (>>=) a b =
    F.make_lit F.Le [b; a]

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

let rec collect_arrows exp =
    match exp.texpr_desc with
    | TE_arrow (e1, e2) ->
        let arr, body = collect_arrows e2 in
        e1 :: arr, body
    | _ -> [], exp

let f_or formulae =
    match formulae with
    | []  -> F.f_false
    | [f] -> f
    | l   -> F.make F.Or l

let f_and formulae =
    match formulae with
    | []  -> F.f_true
    | [f] -> f
    | l   -> F.make F.And l

let rec expression_to_formula nodes prefix ({texpr_desc} as exp) ~time =
  match texpr_desc with
  | TE_const (Cbool b) ->
     f_bool b, []
  | TE_ident {name} ->
     ((prefix ^ name) @@@ [time]) === (t_bool true), []
  | TE_op (Op_if, [cond; thn; els]) ->
     let cond, ec = expression_to_formula nodes prefix cond time in
     let f1, e1 = expression_to_formula nodes prefix thn time in
     let f2, e2 = expression_to_formula nodes prefix els time in
     (cond &&& f1) ||| ((!!cond) &&& f2), (ec @ e1 @ e2)
  | TE_op (op, exprs) when is_logic op ->
     let exprs, eqs = split @@ List.map (expression_to_formula nodes prefix ~time:time) exprs in
     f_operation op exprs, List.concat eqs
  | TE_op (op, exprs) when is_comparison op ->
     let exprs, eqs = split @@ List.map (expression_to_terms nodes prefix ~time:time) exprs in
     f_compare op (List.map List.hd exprs), List.concat eqs
  | TE_arrow (head, tail) ->
     let initials, body = collect_arrows exp in
     let equations = ref [] in
     let conds = List.mapi (fun i expr ->
         let f, eqs = expression_to_formula nodes prefix expr (t_int 0) in
         equations := eqs @ !equations;
         (time === (t_int i)) &&& f)
         initials
     in
     let body, eqs = expression_to_formula nodes prefix body time in
     f_or ((time >>> (t_int (List.length conds))) :: conds), eqs @ !equations

  | TE_pre f ->
     let f, fe = expression_to_formula nodes prefix f (time (*-- (t_int 1*)) in
     (time >>> (t_int 0)) => f, fe

  | _ ->
     Typed_ast_printer.print_exp Format.std_formatter exp;
     Format.fprintf Format.std_formatter "%!";
     failwith "failure"
and expression_to_terms nodes prefix ({texpr_desc} as exp) =
  match texpr_desc with
  | TE_const (Cint i) ->
     fun ~time ->
     [t_int i], []
  | TE_const (Cbool b) ->
     fun ~time ->
     [t_bool b], []
  | TE_const (Creal r) ->
     fun ~time ->
     failwith "We can't handle reals yet"
  | TE_ident {name} ->
     fun ~time ->
     [(prefix ^ name) @@@ [time]], []
  | TE_op (Op_if, [cond; thn; els]) ->
     let f_cond = expression_to_formula nodes prefix cond in
     let f_thn = expression_to_terms nodes prefix thn in
     let f_els = expression_to_terms nodes prefix els in
     fun ~time ->
         let cond, cnd_eq = f_cond time  in
         let thn, thn_eq = f_thn time in
         let els, els_eq = f_els time in
         List.map2 (ite cond) thn els, cnd_eq @ thn_eq @ els_eq 
  | TE_op (op, exprs) when is_arith op ->
     let results = List.map (expression_to_terms nodes prefix) exprs in
     fun ~time ->
         let results = List.map (fun f -> f ~time:time) results in
         let exprs = List.map List.hd (List.map fst results) in
         let eqs = List.concat (List.map snd results) in
         [t_operation op exprs], eqs 
  | TE_op (op, exprs) when is_logic op ->
     let f_formula = expression_to_formula nodes prefix exp in
     fun ~time ->
         let name = fresh () in
         declare name Type.type_bool;
         let formula, eqs = f_formula time in
         [ name @@@ [time] ], ((name @@@ [time] === (t_bool true)) <=> formula) :: eqs
  | TE_op (op, [e1; e2]) when is_comparison op ->
     let f_formula = expression_to_formula nodes prefix exp in
     fun ~time ->
         let name = fresh () in
         declare name Type.type_bool;
         let formula, eqs = f_formula time in
         [name @@@ [time]], (((name @@@ [time]) === (t_bool true)) <=> formula) :: eqs

  | TE_arrow (e1, e2) ->
     let initial, body = collect_arrows exp in
     let f_initial = List.map (expression_to_terms nodes prefix) initial in
     let f_body = expression_to_terms nodes prefix body in
     fun ~time ->
         let initial_terms, initial_eqs = split
            (List.mapi (fun i f -> f ~time:(t_int i)) f_initial)
         in 
         let body_term, body_eqs = f_body ~time:time in
         let term = ref (List.hd initial_terms) in
         List.iteri (fun i elt ->
             term := List.map2 (ite (time === (t_int i))) !term elt)
             (List.tl initial_terms);
         List.map2 (ite (time >>= (t_int @@ List.length initial_terms))) body_term !term
         , List.concat (body_eqs :: initial_eqs)

  | TE_pre e ->
     let f_terms = expression_to_terms nodes prefix e in
     fun ~time ->
     let terms, equations = f_terms (time -- (t_int 1)) in
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
     let f_results = List.map (expression_to_terms nodes prefix) exprs in
     fun ~time ->
         let results = List.map (fun f -> f ~time:time) f_results in
         let terms = List.concat @@ List.map fst results in
         let eqs = List.concat @@ List.map snd results in
         terms, eqs

  | TE_app ({name}, args) ->
	 let new_prefix = fresh ~prefix:"call#" () in
     let f_args = List.map (expression_to_terms nodes prefix) args in
     begin
     try
         let node = List.find (fun {tn_name={name=name'}} -> name = name') nodes in
         let f_node_eqs = node_to_formulae nodes new_prefix node in
         fun ~time ->
             let args, arg_eqs = split (List.map (fun f -> f ~time:time) f_args) in
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
             let node_eqs = f_node_eqs ~time in

             results, input_eqs @ node_eqs
     with Not_found ->
        failwith ("No such node " ^ name)
     end
  | TE_prim ({name}, _) ->
     failwith ("What is prim " ^ name)
  | _ ->
     failwith "something went wrong"

and equation_to_formulae nodes prefix {teq_patt; teq_expr} =
  let f_exprs = expression_to_terms nodes prefix teq_expr in
  fun ~time -> 
      let exprs, eqs = f_exprs time in
          List.map2 (fun {name} expr -> (prefix ^ name) @@@ [time] === expr)
                teq_patt.tpatt_desc
                exprs
          @ eqs

and node_to_formulae nodes prefix {tn_equs} =
    let f_equs = List.map (equation_to_formulae nodes prefix) tn_equs in
    fun ~time ->
        List.map (fun f -> f ~time:time) f_equs |> List.concat
	    
let declare_variables {tn_input; tn_output; tn_local; tn_equs} =
  let variables = tn_input @ tn_output @ tn_local in
  List.iter (fun ({name}, t) -> declare name (as_smt_type t)) variables
