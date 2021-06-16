open Ftools
open VcpBase
 
(*
module Term = struct
	type t = NIL | VAR of string
	
	(** It supports NIL substitution as well *)
	let substitute (to_be_replaced:t) (replaced_by:t) (_t:t) : t = 
		if _t = to_be_replaced then
			replaced_by
		else
			_t  

	let encode = function
		| "nil" -> NIL
		| x -> VAR x
							
	let decode = function
		| NIL -> "nil"
		| VAR s -> s

	let find term strs : t = 
		List.find ((=) term) (encode |>>| strs) 
		
	let compare x y = match x, y with 
	| NIL, _ -> 1
	| _, NIL -> -1
	| VAR a, VAR b -> Bytes.compare a b


	let print = function
		| NIL -> pw "Term.NIL"
		| VAR x -> pw "Term.VAR "; ps x

	let pprint = function
		| NIL -> pw "nil"
		| VAR x -> pw x


end;;

module BExp  = struct
	type t = 
		| EQ of Term.t * Term.t 
		| NEQ of Term.t * Term.t
	
	let substitute (to_be_replaced : Term.t) (replaced_by : Term.t) = function
		| EQ (_ta, _tb) -> 
				EQ (
					Term.substitute to_be_replaced replaced_by _ta, 
					Term.substitute to_be_replaced replaced_by _tb)
		| NEQ (_ta, _tb) -> 
				NEQ (
					Term.substitute to_be_replaced replaced_by _ta, 
					Term.substitute to_be_replaced replaced_by _tb) 
	
	let dual = function
			| EQ (a,b) -> NEQ (a,b)
			| NEQ (a,b) -> EQ (a,b)
	
	let rev = function
			| EQ (a,b) -> EQ (b,a)
			| NEQ (a,b) -> NEQ (b,a)
	
	let fv = function
		| EQ (a,b) when a=b -> [a]
		| EQ (a,b) -> [a; b]
		| NEQ (a,b) -> [a; b]

	let is_consistent = function
		| EQ (a, b) -> a = b
		| NEQ (a, b) -> a <> b

	let is_contradict = function
		| EQ (a, b) -> false
		| NEQ (a, b) -> a = b

	let in_structure pointers a b = 
		s_or (fun (x, ys) -> (a = x && b |<- ys) || (b = x && a |<- ys)) pointers 
	 
	let non_trivial t_exqs (pre_locations, post_locations) pointers eq = 
		match eq with
		| EQ (a, b) when a = b -> false 
		| EQ (a, b) when (a |<- t_exqs) || (b |<- t_exqs) -> false
		| NEQ (a, b) when (a |<- t_exqs) || (b |<- t_exqs) -> false
		| NEQ (a, b) when 
			((a |<- pre_locations) && (b |<- pre_locations)) && a<>b -> false 
(*		| NEQ (a, b) when (in_structure pointers a b) && a <> b -> false *) 
		| NEQ (a, Term.NIL) | NEQ (Term.NIL, a) -> 
			if a |<- pre_locations then  
				false
			else
				true 
		| _ -> true

	let print = function
		| EQ (t1, t2) -> (pw "BExp.EQ ("; Term.print t1; pw ","; Term.print t2; pw ")")
		| NEQ (t1, t2) -> (pw "BExp.NEQ ("; Term.print t1; pw ","; Term.print t2; pw ")")

	let pprint = function
		| EQ (t1, t2) -> Term.pprint t1; pw "="; Term.pprint t2
		| NEQ (t1, t2) -> Term.pprint t1; pw "=/"; Term.pprint t2

	let compare x y = match x, y with
	| EQ (a,b), EQ (c,d) -> if (a = c && b = d) || (a = d && b = c) then 0 else -1
	| NEQ (a,b), NEQ (c,d) -> if (a = c && b = d) || (a = d && b = c) then 0 else -1
	| _ -> -1 
	
	(*
	let (==) a b = match a, b with
	| EQ (x, y), EQ (z, w) -> x = z && y = w
	| NEQ (x, y), NEQ (z, w) -> x = z && y = w
	| _ -> false
	*)
end;;

module Pointer = struct
	type t = Term.t * Term.t list

	let location (l, _) = l

	let print (location, elements) = 
		pw "(";
		Term.print location;
		pw ",[";
		iterS (Term.print) ";" elements;
		pw "])";;

	let pprint (location, elements) = 
		Term.pprint location;
		pw "->(";
		iterS (Term.pprint) "," elements;
		pw ")";;
	
	let substitute (to_be_replaced : Term.t) (replaced_by : Term.t) ((location, elements) : t) : t =
		(	Term.substitute to_be_replaced replaced_by location,
			(Term.substitute to_be_replaced replaced_by) |>>| elements 
		)
		
	let is_consistent ((location, _) : t) = location <> Term.NIL
	
	let contained_in s_var (location, elements) =
		let t_var = Term.encode s_var in
		t_var = location || (List.exists ((=) t_var) elements)

	(*	
		Input : [x y z], (a, [b x c z]), (a, [b d c y])
		Output: true 
		*)	
	let partial_match post_exqs pre_exqs (location_b, elements_b) (location_a, elements_a) : bool =
		let t_pre_exqs = Term.encode |>>| pre_exqs in
		let t_post_exqs = Term.encode |>>| post_exqs in
		let f_match = fun a b -> 	if b |<- t_post_exqs then
																(true, Some (b, a))
															else if a |<- t_pre_exqs then
																(true, None)  (** (isMatching, Some (Quantifier Term, Actual value)) *) 
															else 
																(a = b, None)									
		in  
		let rec is_match_consistent matches = 
			match matches with
			| [] -> true
			| (x,y)::t -> (fun (z,w) -> z <> x || y = w) |>>| t >> l_and && (is_match_consistent t) 
		in
		let location_match = f_match location_a location_b in
  	let result = if List.length elements_a =  List.length elements_b then
    		let elements_match = List.map2 f_match elements_a elements_b in
    		if fst |>>| (location_match :: elements_match) >> l_and then
      		let valid_matches = (snd |>>| (location_match :: elements_match)) >> valids_only in
      		if is_match_consistent valid_matches then
      			begin true (* valid_matches *) end
      		else
      			begin false (* [] *) end   
    		else
    			begin false (* [] *) end
  		else 
  			begin false (* [] *) end
		in 
		result

	let get_value var (loc, elems) (m_loc, m_elems) : Term.t = 
		let tvar = Term.encode var in
		let f a b c = 
			begin
			match a with 
			| Term.NIL -> if b = tvar then c else a
			| _ -> a
			end 
		in
		if tvar = loc then 
			m_loc
		else
			List.fold_left2 f Term.NIL elems m_elems
		
	let realize_value_from_ptr exqs b_exqs var base_ptrs (loc, elems) : Term.t list = 
		let tvar = Term.encode var in
		if tvar = loc || (tvar |<- elems) then
			begin
			pprint (loc, elems);
			let matched_ptrs : (Term.t * Term.t list) list = List.filter (partial_match exqs b_exqs (loc, elems)) base_ptrs in
			pw (string_of_int (List.length matched_ptrs)); pw ": ";
			let possible_values :  Term.t list = get_value var (loc, elems) |>>| matched_ptrs in
			possible_values
			end
		else
			[]
	
			(* a variable and its possible values *)		
	let realize_value exqs b_exqs bases ptrs var : string * Term.t list = 
		pw "realizing "; pw var; pw "... "; 
		let x : Term.t list = realize_value_from_ptr exqs b_exqs var bases |>>| ptrs >> List.concat in
		let y : Term.t list = List.sort_uniq Term.compare x in
		if y <> [] then pw (Term.decode (List.hd y)); pw "\n";
		(var, y)


(*	let translate (str, _, exps) = 
		Term.encode str, () |>>| exqs *)

end;;	

module Predicate = struct
	type t = string * Term.t list
	
	let substitute (to_be_replaced : Term.t) (replaced_by : Term.t) ((name, elements) : t) : t =
		(	name,
			(Term.substitute to_be_replaced replaced_by) |>>| elements 
		)

	let fvs (_, t_list) = Term.decode |>>| t_list

	let print (name, arguments) = 
		pw "(";
		ps name;
		pw ",[";
		iterS Term.print ";" arguments;
		pw "])";;
	
	let pprint (name, arguments) = 
		pw name;
		pw "(";
		iterS Term.pprint "," arguments;
		pw ")";;


(*	let translate (str, exps) = 
		(str, () |>>| exps) *)
end;;

module Formula = struct
	type t = string list * BExp.t list * Pointer.t list * Predicate.t list
	
	let empty = ([], [], [], [])
	
	let merge (a1,b1,c1,d1) (a2,b2,c2,d2) = (a1@a2, b1@b2, c1@c2, d1@d2) 
		
	let is_equal (exqs1, eqfs1, ptrs1, preds1) (exqs2, eqfs2, ptrs2, preds2) =
		List.length exqs1 = List.length exqs2 && 
		ptrs1 |==| ptrs2 && 
		preds1 |==| preds2 &&
		List.length eqfs1 = List.length eqfs2
		 
	(** This is blind substitution *)
	let substitute (to_be_replaced : Term.t) (replaced_by : Term.t) 
								 ((existential_quantifiers, eqformulas, pointers, predicates) : t) : t =
 		(	(fun x -> if replaced_by <> Term.NIL && Term.decode to_be_replaced = x then Term.decode replaced_by else x ) |>>| existential_quantifiers, 
			(BExp.substitute to_be_replaced replaced_by) |>>| eqformulas,
			(Pointer.substitute to_be_replaced replaced_by) 	|>>| pointers, 
			(Predicate.substitute to_be_replaced replaced_by) |>>| predicates
		)
	
	let (:=) ((existential_quantifiers, eqformulas, pointers, predicates) : t)
								  		(to_be_replaced : Term.t) (replaced_by : Term.t) : t =
		let _formula = 
			if replaced_by <> Term.NIL then
				let s_replaced_by = Term.decode replaced_by in 
				if s_replaced_by |<- existential_quantifiers then 
  				let _s_replaced_by = newvar s_replaced_by in
  				let _existential_quantifiers = (s_replaced_by := _s_replaced_by) |>>| existential_quantifiers in
  				let _replaced_by = Term.encode _s_replaced_by in
  				substitute 	replaced_by _replaced_by 
  										(_existential_quantifiers, eqformulas, pointers, predicates)
  			else
				(existential_quantifiers, eqformulas, pointers, predicates)	
			else
			(existential_quantifiers, eqformulas, pointers, predicates)			
		in
		substitute 	to_be_replaced replaced_by _formula
	
	(** Context free consistency checking *)
	let is_consistent ((existential_quantifiers, eqformulas, pointers, predicates) : t) : bool =
		let is_eqformula_consistent = BExp.is_consistent |>>| eqformulas >> l_and in
		let is_pointers_consistent = Pointer.is_consistent |>>| pointers >> l_and in
		is_eqformula_consistent && is_pointers_consistent
			 	
	let unfold (args : Term.t list) (params : string list) (formula : t) : t =
		let term_params = Term.encode |>>| params in
		List.fold_left2 (:=) formula term_params args
				
	let matched (args : Term.t list) (params : string list) (formula : t) : t option =   
		let applied_formula = unfold args params formula in
		if is_consistent applied_formula then
			Some applied_formula
		else
			None  
	
	
	let drop_pure lpointers all_pointers ((exqs, eqformulas, pointers, predicates) : t) : t = 
		let t_exqs = Term.encode |>>| exqs in
		let _eqformulas = List.filter (BExp.non_trivial t_exqs lpointers all_pointers) eqformulas in
		(exqs, _eqformulas, pointers, predicates)
		
	let print (exqs, eqformulas, pointers, predicates) =
		pw "([";
		iterS ps ";" exqs;
		pw "],[";
		iterS BExp.print ";" eqformulas;
		pw "],[";
		iterS Pointer.print ";" pointers;
		pw "],[";
		iterS Predicate.print ";" predicates;
		pw "])"
		
		
	let pprint (exqs, eqformulas, pointers, predicates) =
		if List.length exqs > 0 then
			begin
			pw "Ex ";
			iterS pw " " exqs;
			pw ".";
			end
		else
			pw "";
		iterS BExp.pprint " & " eqformulas;
		if List.length eqformulas > 0 then
			pw " & "
		else
			pw "";
		iterS Pointer.pprint " * " pointers;
		if List.length pointers > 0 && List.length predicates > 0 then
			pw " * "
		else if List.length pointers = 0 && List.length predicates = 0 then
			pw "Emp"
		else 
			pw "";
		iterS Predicate.pprint " * " predicates;;

(*		let translate (exqs, eqs , _ , comp_l , preds) =
			 (exqs, () |>>| eqs , () |>>| comp_l, () |>>| preds) *)
end;;
*)

module PredicateDefinition = struct
	type t = string * string list * Formula.t list

	let matched ((name_a, args) : Predicate.t) ((name_b, params, formulas) : t) : Formula.t option =
		if name_a = name_b then
			(Formula.matched args params) |>>| formulas >> valid
		else
		None
    
			
	let print (name, parameters, defs) =
		pw "(";
		ps name;
		pw ",[";
		iterS ps ";" parameters;
		pw "],[";
		iterS Formula.print ";" defs;
		pw "])"
		
end;;

module PredicateDefinitions = struct 
	type t = PredicateDefinition.t list
	
	(** Matched by substitution and validity check  *)
	let matched (pred : Predicate.t) (preddefs: t) : Formula.t option =
		(PredicateDefinition.matched pred) |>>| preddefs >> valid
		
	let print x = 
		pw "[";
		iterS PredicateDefinition.print ";" x;
		pw "]"
		 
end;;	



module Entailment = struct
	type t = Formula.t * Formula.t

	let merge (pre1, post1) (pre2, post2) = (Formula.merge pre1 pre2, Formula.merge post1 post2)
			
	let empty : (int * t) list = []
	
	let pprint (pre, post) =
		Formula.pprint pre; pw " |- "; Formula.pprint post;;

	type stack = {
		mutable content : (int * t) list
	}
	
	let olds : stack = { content = [] }
	
	let is_too_much = List.length olds.content > 6
	
	let push entailment = olds.content <- (((List.length olds.content) + 1, entailment) :: olds.content)
	
	let pop () = olds.content <- List.tl olds.content
	
	let is_equal (precondition1, postcondition1) (n, (precondition2, postcondition2)) =
		  n <> (List.length olds.content) && 
			Formula.is_equal precondition1 precondition2 &&
			Formula.is_equal postcondition1 postcondition2
	
	let is_old entailment = List.exists (is_equal entailment) olds.content 
	
	let pattern_match (((_,_,_,pr_a), (_,_,_,pr_b)) as tm) (((q_1,e_1,pt_1,pr_1), (q_2,e_2,pt_2,pr_2))) = 
		let arg_ls = fun (_,ts) -> ts in
		let all_args a b = (List.concat (arg_ls |>>| a)) @ (List.concat (arg_ls |>>| b)) in
		let xab = uniq (all_args pr_a pr_b) in
		let x12 = uniq (all_args pr_1 pr_2) in
		let subs (fa, fb) tbr rb = (Formula.usubstitute tbr rb fa Locs.dummy, Formula.usubstitute tbr rb fb Locs.dummy) in 
		if List.length xab = List.length x12 then
			let ((q_a,e_a,pt_a,pr_a), (q_b,e_b,pt_b,pr_b)) = (List.fold_left2 subs tm xab x12 ) in
			q_a |==| q_1 && q_b |==| q_2 && 
			e_a |==| e_1 && e_b |==| e_2 && 
			pt_a |==| pt_1 && pt_b |==| pt_2 && 
			pr_a = pr_1 && pr_b = pr_2
		else
			false
			
	let upattern_match_all_combination 
						((q_a,e_a,pt_a,pr_a), (q_b,e_b,pt_b,pr_b)) 
						(n, (((q_1,e_1,pt_1,pr_1), (q_2,e_2,pt_2,pr_2)) as tmw)) =  
		if n = (List.length olds.content) then false else
		let el x y = List.length x = List.length y in
		if 	el q_a q_1 && el q_b q_2 && 
				el e_a e_1 && el e_b e_2 && 
				el pt_a pt_1 && el pt_b pt_2 && 
				el pr_a pr_1 && el pr_b pr_2 
		then
			let combs = ((permute pr_a) >><< (permute pr_b)) in
			let nm = (fun (n,_) -> n) in
			let name_match (x_a, x_b) (x_1,x_2) = (nm |>>| x_a) = (nm |>>| x_1) && (nm |>>| x_b) = (nm |>>| x_2) in
			let combs' = List.filter (name_match (pr_1, pr_2)) combs in
			let entls = (fun (a,b) -> ((q_a,e_a,pt_a,a),(q_b,e_b,pt_b,b))) |>>| combs' in
			let result = s_or (pattern_match tmw) entls in
			if result then pw ""; result   
		else
		false

 let pattern_match_all_combination 	(fa, fb) (n, (f1, f2)) =  
	false
	
	let diversing () = 
	 if olds.content <> [] then
    let (a,b) = (snd (List.find (fun (n,_) -> n = 1) olds.content)) in
    let (_, _, pt_a, pr_a) = List.hd a in
    let (_, _, pt_b, pr_b) = List.hd b in
    let m = (List.length pt_a)  + (List.length pt_b) + (List.length pr_a) + (List.length pr_b) in
		m*3 < (List.length olds.content)
	else
	 false


	let udrop_the_commons ((a,b,c,d), (e,f,g,h)) = 
		let (b',f') = drop_common b f in
		let (c',g') = drop_common c g in
		let (d',h') = drop_common d h in
	((a,b',c',d'), (e,f',g',h'))

 let drop_the_commons ((a, b) : t) =
   List.split (List.map2 (fun a b -> udrop_the_commons (a, b)) a b)
								
	let check_old (entailment : t) = 
		pw "Level "; pw (string_of_int (List.length olds.content)); pw "\n";
		let b = is_old entailment in
		pw "Checked... \n";
		if b then 
			begin
				pw "it is old (false)\n";
				Some false 
			end
		else if diversing () then
			begin
				pw "it is diversing (false)\n";
				Some false 
			end
		else 
			let (entailment : t) = (drop_the_commons entailment) in
			if s_or (pattern_match_all_combination entailment) olds.content then
			begin
				pw "PATTERN CHECKING: "; pprint entailment; pw "\n";
				pw "Pattern Matched with Old (true)\n";
				Some true 
			end
		else
			begin
				pw "Continue...\n";
				None 
			end
			
	type maybe_eqs  = {
		mutable eqs_l : BExp.t list
	}
	
	let maybe_eqs = { eqs_l = [] }
	
	type ptr_locations = {
		mutable pre : Term.t list;
		mutable post: Term.t list
	}
	
	let locs = { pre = []; post = [] }
	
	let ulocs_update precondition postcondition = 
		let (pre_exqs, _, pre_ptrs, _) = precondition in
		let (post_exqs, _, post_ptrs, _) = postcondition in
		let pre_ptrs' = (fun (x, _) -> x) |>>| pre_ptrs in
		let post_ptrs' = (fun (x, _) -> x) |>>| post_ptrs in
		let pre_locs = List.filter (fun x -> not ((Term.toStr x) |<- pre_exqs)) pre_ptrs' in
		let post_locs = List.filter (fun x -> not (Term.toStr x |<- post_exqs)) post_ptrs' in
		locs.pre <- List.sort_uniq (Term.compare) (locs.pre @ pre_locs);
		locs.post <- List.sort_uniq (Term.compare) (locs.post @ post_locs);
		pw "locs: ";
		iterS Term.pprint ", " locs.pre; 
		pw "\n"

 let locs_update ((precondition : Formula.t), (postcondition : Formula.t)) =
   List.iter2 ulocs_update precondition postcondition
	
	let substitute ((precondition, postcondition) : t) = function 
		| BExp.UNIT (_, Op.NE, _) -> 				( precondition, postcondition )
		| BExp.UNIT (a, Op.EQ, Term.NULL) -> 	( Formula.(:=) precondition a Term.NULL, Formula.(:=) postcondition a Term.NULL )
	| BExp.UNIT (a, Op.EQ, b) ->  				( Formula.(:=) precondition b a, Formula.(:=) postcondition b a )
 | _ -> raise Error
	(** CAUTION: Non-exhaustive *)
	
	let normalize entailment = 
		let (_, pre_eqformulas, _, _) = List.hd (fst entailment) in
		substitute |->> (entailment, pre_eqformulas)

		(*		
	(** At this point a quantifier may have more than one value. We should try all until we get consistency *)
	let partial_matches exqs pre_pointers pointer = 
		(Pointer.partial_match exqs pointer) |>>| pre_pointers >> List.concat 	
	*)
		
		(*
	(** This is pointer structure based realization. Predicate call based realization may be needed to implement as well but not sure *)		
	let realize_existential_quantifier pre_pointers ((exqs, es, post_pointers, ps) as postcondition) exq =
		match List.filter (Pointer.contained_in exq) post_pointers with
		| [] -> postcondition
		| container_pointers ->  
			begin
			match (partial_matches exqs pre_pointers) |>>| container_pointers >> List.concat with
			| [] -> pw "UNSAT \n"; raise (NoRealizationForQuantifier (exq))		(** UNSAT condition because no matching found *)
			| matched_pairs -> 	
				begin
				match List.filter (fun (a,b) -> Term.decode a = exq) matched_pairs with
				| [] -> raise Error (** Very Unusual *)
				| (qvar, value)::_ -> (** One combination try only. Not backtracing in pattern matching to try to match other variant *)
															Formula.(:=) postcondition qvar value
				end
			end;;       
*)

(*
	(** This is a heuristic function and tries once only. Needed to be general/concrete *)
	let realize_existential_quantifiers (precondition, postcondition) = 
		let (_, _, pre_ptrs, _) = precondition in
		let (exqs, _, post_ptrs, _) = postcondition in
		let (_, _eqformulas, _ptrs, _preds) = (realize_existential_quantifier pre_ptrs) |->> (postcondition, exqs) in
		(precondition, ([], _eqformulas, _ptrs, _preds)) (* It is best if only realized qvars are removed  *)
*)
	
	let drop_matched ((pre_exqs, pre_eqformulas, pre_pointers, pre_predicates), 
										(post_exqs, post_eqformulas, post_pointers, post_predicates)) = 
		let (_pre_eqformulas, _post_eqformulas) = drop_common pre_eqformulas post_eqformulas in
(*	let (_pre_pointers, _post_pointers) = drop_common pre_pointers post_pointers in
		let (_pre_predicates, _post_predicates) = drop_common pre_predicates post_predicates in
		((pre_exqs, _pre_eqformulas, _pre_pointers, _pre_predicates), (post_exqs, _post_eqformulas, _post_pointers, _post_predicates))
*)
		((pre_exqs, pre_eqformulas, pre_pointers, pre_predicates), (post_exqs, _post_eqformulas, post_pointers, post_predicates))

	let alpha_if oexqs (exs, eqformulas, pointers, predicates) exq = 
		(* if exq |<- oexqs then *)
			let new_exq = newvar exq in
			List.hd (Formula.(:=) [(exs, eqformulas, pointers, predicates)] (Term.encode_str exq) (Term.encode_str new_exq))
		(* else
			(exs, eqformulas, pointers, predicates) *)

	let unfold_with_alpha (oexq, post_eqformulas, post_pointers, post_predicates) (exs, eqformulas, pointers, predicates) predicate =
		let rest_post_predicates = List.filter (fun x -> x <> predicate) post_predicates in
		let (exs, eqformulas, pointers, predicates)  = ((alpha_if oexq) |->> ((exs, eqformulas, pointers, predicates), exs)) in
		(exs @ oexq, post_eqformulas @ eqformulas, post_pointers @ pointers, rest_post_predicates @ predicates) 
	
	let unfold_a_predicate preddefs old_formula predicate = 
		match PredicateDefinitions.matched predicate preddefs with
		| None -> old_formula  (* It will never happen *)
		| Some unfolded_formula -> 
			unfold_with_alpha old_formula unfolded_formula predicate
			
	(*
	let unfold preddefs (	((_, pre_eqformulas, pre_pointers, pre_predicates) as precondition), 
												((_, post_eqformulas, post_pointers, post_predicates) as postcondition)) =
												if List.length pre_pointers = 0 && List.length pre_pointers > 0 && List.length post_pointers > 0 then
													(((unfold_a_predicate preddefs) |->> (precondition, pre_predicates)), postcondition)
												else
													(precondition, ((unfold_a_predicate preddefs) |->> (postcondition, post_predicates))) (** May be decision based unfolding is better *)
	*)

	let is_proved 	
									((_, _, pre_pointers, pre_predicates), 
									(_, post_eqformulas, post_pointers, post_predicates)) = 
		List.length post_eqformulas = 0 && pre_pointers = post_pointers && pre_predicates = post_predicates
			
	
(*
	let insufficient_memory ((_, _, pre_pointers, pre_predicates), (_, _, post_pointers, _)) = 
		if List.length pre_pointers + List.length pre_predicates = 0 && List.length post_pointers > 0 then
			true
		else
			let locations = (fun (Term.VAR x, _) -> x) |>>| post_pointers in
			let uniqlocs = List.sort_uniq Bytes.compare locations in
			locations <> uniqlocs

	let rec prove2 preddefs ((precondition, postcondition) as entailment) =
		pw "\nStart .\n";
		pprint (precondition, postcondition); pw "\n";
		(** a=b ^ A |- B --> A[a:=b] |- B[a:=b] *)
		let _entailment = normalize entailment in 
		pprint _entailment; pw "         (equality reduced in both sides)\n"; 
		(** a->(b,c) |- Ex x.a->(x,c) --> x=b --> a->(b,c) |- a->(b,c) *)
		if insufficient_memory _entailment then
			(pw "Heap mismatch. "; false)
		else
			begin
  		let __entailment = realize_existential_quantifiers _entailment in
  		(** a=b & c=d & a->(b,c) * p(a,c) |- a=b & a->(b,c) * p(a,c) * q(d) --> c=d |- q(d) *) 
  		let (_, _, pre_pointers, _) = fst __entailment in
  		let (_, _, post_pointers,_) = snd __entailment in
  		let pointers = pre_pointers @ post_pointers in 
  		pprint __entailment; pw "         (quantifiers realization)\n"; 
  		let ___entailment = drop_matched __entailment in
  		pprint ___entailment; pw "         (dropped matching memory segments)\n";  
  		let ____entailment = (Formula.drop_pure pointers (fst ___entailment), Formula.drop_pure pointers (snd ___entailment)) in 
  		pprint ____entailment; pw "         (dropped true pure formulas)\n"; 
  		if is_proved ____entailment then
  			true
  		else
  			(** Unfold predicate definitions to 1 more level *)
  			let unfolded_entailment = unfold preddefs ____entailment in
  			pprint unfolded_entailment; pw "         (unfolded)\n"; 
  			if snd entailment = snd unfolded_entailment then (* Not sure. Need to observe *)
  				(pw "Saturated unfolding. "; false)
  			else
  				prove preddefs unfolded_entailment
			end
*)
	
	let rec is_sat n preddefs eQ (exqs, eqs, ptrs, preds) =
		Formula.pprint (exqs, eqs, ptrs, preds); pw "[checking in]\n";
		if n > 20 then false else
		let fv = Term.encode_str |>>| (BExp.fv eQ) in 
		let false_neq = function
			| BExp.UNIT (a, Op.NE, b) when a = b -> pw "True NEQ\n"; true
			| _ -> pw "False EQ/NEQ\n"; false
		in
(*		let is_dual_exists eqs eq = 
			let d = BExp.dual eq in (d |<- eqs) || ((BExp.rev d) |<- eqs)
		in *)
		(** Inner functions *)
		let get_important_pred preds : Predicate.t list =
			List.filter (fun (_, params) -> List.exists (fun v -> v |<- params) fv) preds
		in
(*		let exqs_less exqs preds = 
			let t_exqs = Term.encode |>>| exqs in
			List.filter (fun (_, params) -> not (List.exists (fun v -> v |<- params) t_exqs)) preds
		in *)
		let unfold_and_try (pred_name, args) precondition =
			let (_, params, formulas) = try List.find (fun (n,_,_) -> n = pred_name) preddefs with _ -> raise (StError "Entailment - 1") in
			let r = s_or (fun def ->
				let def' = Formula.unfold args params def in 
				let precondition' : Formula.t = unfold_with_alpha precondition def' (pred_name, args) in
				is_sat (n+1) preddefs eQ precondition' 
				) formulas in
			r
		in
		(** Start of main body *)
		let t_exqs = Term.encode_str |>>| exqs in
		(** If a single pointer is existential variable, then terminate and return false, because it may be nil *)
		if List.exists (fun (x,_) -> x |<- t_exqs) ptrs then
			begin
				pw "True EXIST\n";
			true
			end
		else
		(** Normalize by substitution *)	
		let (exqs, eqs, ptrs, preds) = (fun f x -> 
				match x with
				| BExp.UNIT (a, Op.EQ, b) -> if a |<- fv then Formula.(:=) f b a else Formula.(:=) f a b
				| BExp.UNIT (_, Op.NE, _) -> f
				(*| BExp.OP ?? *)) 
			|->> ((exqs, eqs, ptrs, preds), eqs) in
		(** If a =/ a then return false *)
		Formula.pprint (exqs, eqs, ptrs, preds); pw "[subs]\n";
		if List.exists false_neq eqs then
			false 
(*		else if List.exists (is_dual_exists eqs) eqs then
			false *)
		else 
			(** Collect the locations *)
			let locations = Pointer.location |>>| ptrs in
			(** If a location exists twict, return nil *)
			if has_duplicate locations then
				begin
					pw "False DUP LOC\n";
				false
				end
			(** If no more predicates, it is satisfiable *)
			else if preds = [] then
				begin
				Formula.pprint (exqs, eqs, ptrs, preds); pw " is SAT\n";
				true
				end
			else
				(** Try to get important predicates *)
				let preds' = get_important_pred preds in
				if preds' = [] then
					unfold_and_try (List.hd preds) (exqs, eqs, ptrs, preds)
				else
					unfold_and_try (List.hd preds') (exqs, eqs, ptrs, preds)
	
	let is_not_ok preddefs formula eq =
		let d_eq = BExp.complement eq in
		pw "SAT checking: "; BExp.pprint d_eq; pw "\n";
		(is_sat 0 preddefs d_eq (Formula.merge ([],[d_eq],[],[]) formula)) 
		
(*  commented for experimentation *)
 	let drop_pure preddefs _locs all_pointers (precondition, postcondition) =
		let (exqs, eqs, ptrs, preds) = postcondition in
(*		let (_, (formula, _)) = List.find (fun (n,_) -> n = 1) olds.content in *)
		let eqs' = List.filter (is_not_ok preddefs precondition) eqs  in
		 (Formula.drop_pure _locs all_pointers (precondition), 
			Formula.drop_pure _locs all_pointers (exqs, eqs', ptrs, preds)) 

	let get_realized_pairs (b_exqs, _, b_ptrs, _) (exqs, _, ptrs, _) : (Var.t * Term.t) list list = 
		(* pw (string_of_int (List.length exqs)); pw "\n"; *)
		(** list of (variable name, list of possible values ) [("@1", [x;y;z]) ; ("@2", [w;v])] *)
		let vars_with_values : (Var.t * Term.t list) list = Pointer.realize_value exqs b_exqs b_ptrs ptrs |>>| (Var.encode Var.EXQ |>>| exqs) in
		(** list of combinations of list of (variable name, a possible value) [[("@1",x);("@2",w)] ; [("@1",x);("@2",v)] ; ...] *)
		cross vars_with_values				

	let update_vars formula (to_be_replaced, replaced_by) = 
		let (_, _eqformulas, _pointers, _predicates) = 
			Formula.substitute (Term.encode to_be_replaced) replaced_by formula Locs.dummy in
		let (exqs, _, _, _) = formula in
		let tbr = Var.decode to_be_replaced in 
		(	List.filter ((<>) tbr) exqs, _eqformulas, _pointers, _predicates )
	
	
	let is_heap_mismatch (	(_, _, pre_pointers, pre_predicates), 
												(_, _, post_pointers, post_predicates)) =																																																																														
		pre_predicates = [] && post_predicates = [] && pre_pointers <> post_pointers (* ||
		pre_predicates = [] && post_predicates = [] && pre_pointers = [] || 
		pre_predicates = [] && post_predicates = [] && post_pointers = []				*)	
											
	let is_contradict (_, eqs, _, _) = List.exists (BExp.is_contradict) eqs	
	
	let get_all_pointers () = List.concat ((fun (_,((_,_,x,_),(_,_,y,_))) -> x @ y) |>>| olds.content)
	
	let unfolded_true preddefs predicate = 
		let formula = unfold_a_predicate preddefs ([],[],[],[predicate]) predicate in 
		let all_pointers = get_all_pointers () in
		let formula' = Formula.drop_pure (locs.pre, locs.post) all_pointers formula in
		formula' = ([],[],[],[])

	let rec is_loc preddefs ((_, _, _, preds) as formula:Formula.t) var = 
		(*Term.pprint var; pw ":\n";*)
		let check_one (pred_name, args) = 
			let (_, params, defs) = List.find (fun (n,_,_) -> n = pred_name) preddefs in
			let check_all def =
				let def' = Formula.unfold args params def in
				let (exqs1, eqs1, ptrs1, preds1) = unfold_with_alpha formula def' (pred_name, args) in
				let il = List.exists (fun (x, _) -> x = var) ptrs1 in
				if il then 
    			begin
(*    				Term.pprint var; pw " is a loc in "; Formula.pprint (exqs1, eqs1, ptrs1, preds1); pw "\n"; *)
    				true
    			end
    		else
					begin
(*      			Term.pprint var; pw " is not a loc in "; Formula.pprint (exqs1, eqs1, ptrs1, preds1); pw "\n"; *)
      			let ie = List.filter (fun x -> match x with | BExp.UNIT (a, Op.EQ, b) when not (a = b) -> a=var || b=var | _ -> false) eqs1 in
      			if ie = [] then
      				begin
(*        				Term.pprint var; pw "=_ is not in "; Formula.pprint (exqs1, eqs1, ptrs1, preds1); pw "\n"; *)
								false
      				end
      			else
      				begin
      					let companion = match List.hd ie with | BExp.UNIT (a, Op.EQ, b) when a = var -> b | BExp.UNIT (a,Op.EQ, b) when b = var -> a | _ -> var in
(*      					Term.pprint var; pw "="; Term.pprint companion; pw " is in "; Formula.pprint (exqs1, eqs1, ptrs1, preds1); pw "\n"; *)
      					(* Term.pprint var; pw "="; Term.pprint companion; pw "\n"; *)
								(* maybe_eqs.eqs_l <- List.sort_uniq BExp.compare ((BExp.EQ (var, companion)::maybe_eqs.eqs_l)); *)
								let (exqs2, eqs2, ptrs2, preds2) = Formula.(:=) (exqs1, eqs1, ptrs1, preds1) companion var in 
      					Formula.pprint (exqs2, eqs2, ptrs2, preds2); pw " [substituted]\n";
      					let il = List.exists (fun (x, _) -> x = var) ptrs2 in
        				if il then 
            			begin
(*            				Term.pprint var; pw " is a loc in "; Formula.pprint (exqs2, eqs2, ptrs2, preds2); pw "\n"; *)
            				true 
            			end
            		else
      						begin
									let r = is_loc preddefs (exqs2, eqs2, ptrs2, preds2) var in
									if not r then false else 
										begin 
											
											true
										end
									end
      				end
      			end	
			in
			s_and check_all defs
		in
		let all_preds = List.filter (fun (_, ts) -> var |<- ts) preds in
		s_or (check_one) all_preds
																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																																			 
	let get_locs preddefs ((_, _, ptrs, preds) as formula:Formula.t) = 
		let locs = (fun (x,_) -> x) |>>| ptrs in
		let pred_locs = ((fun (_, ts) -> (fun t -> t) |>>| ts) |>>| preds) >> List.concat in
		let pred_locs = List.filter (fun var -> not (var |<- locs)) pred_locs in
(*		iterS Term.pprint ", " locs;
		pw "\n"; *)
		let ils = (fun l -> let r = is_loc preddefs formula l in (l, r)) |>>| pred_locs in
		let ls = (fun (l,_) -> l) |>>| (List.filter (fun (_,il) -> il) ils) in
		pw "Finally: ";
		iterS Term.pprint ", " ls;
		pw "\n";			
		(locs , ls)

	let local_substitute (precondition, postcondition) = function
			| [] -> pw "No Updating\n"; (precondition, postcondition)
			| [(1, comb)] -> pw "Updating precondition\n";
				let _precondition = update_vars |->> (precondition, comb) in
				(_precondition, postcondition)
			| [(-1, comb)] -> pw "Updating postcondition\n";
				let _postcondition = update_vars |->> (postcondition, comb) in
				(precondition, _postcondition)
			| [(x, comb1); (_, comb2)] -> pw "Updating both side\n";
    		let (pre_comb, post_comb) = if x = -1 then (comb2, comb1) else (comb1, comb2) in
				let (extra, pre_comb) = List.partition (fun (x1, v1) -> (Term.decode v1, Term.encode x1) |<- post_comb) pre_comb in
    		let (pre_exqs, a, b, c) =  precondition in
				let extra_v : bytes list = (fun (x,_) -> Var.decode x) |>>| extra in
				let _pre_exqs = List.filter (fun x1 -> not (x1 |<- extra_v)) pre_exqs in
				let precondition = (_pre_exqs, a, b, c) in
				let _precondition = update_vars |->> (precondition, pre_comb) in
    		let _postcondition = update_vars |->> (postcondition, post_comb) in
    		(_precondition, _postcondition)
			| _ -> (precondition, postcondition)
	
	
	let filter_eqs (_, eqs, _, _) =
		let f = function
			| BExp.UNIT (a, Op.EQ, b) -> 
				let (are, arent) = List.partition (fun x -> (x = BExp.UNIT (a, Op.NE, b) || x = BExp.UNIT (b, Op.NE, a))) maybe_eqs.eqs_l in 
				maybe_eqs.eqs_l <- arent; 
				are
			| BExp.UNIT (a, Op.NE, b) -> 
				let (are, arent) = List.partition (fun x -> (x = BExp.UNIT (a, Op.NE, b) || x = BExp.UNIT (b, Op.NE, a))) maybe_eqs.eqs_l in 
				maybe_eqs.eqs_l <- arent; 
				are
			(** CAUTION: Non-exhaustive *)
		in
		List.map (fun e -> f e) eqs	>> List.concat		
			
	let rec prove preddefs ((precondition, _) as entailment) =	
		pw "\n"; 
		pprint entailment; pw " [to be checked]\n";
		(* match check_old entailment with
		| Some b -> b
		| None -> *)
(*		if (check_maybe postcondition) then
			false
		else *)
			begin	
  		push entailment;
  		locs_update entailment;
  		(** if absurd_in_left entailment then true else *) (* ||- P & E=/E & S |- P' & S' *)
  		if is_contradict precondition then false else 
  		let _entailment = normalize entailment in (** (P & S)[E/x] |- (P' & S')[E/x] ||- P & x=E & S |- P' & S' *)
  		pprint _entailment; pw " [normalized]\n";
			let all_pointers = get_all_pointers () in
  		let __entailment = drop_pure preddefs (locs.pre, locs.post) all_pointers _entailment in (* P & S |- P' & S' ||- P & E=E & S |- P' & S' *)
  		pprint __entailment; pw "   [dropped pure true] \n";
  		let result = realize_quantifiers preddefs __entailment in
  		begin pop (); pw "popped\n"; result end
			end
	
	and check_maybe (_, eqs, _, _) = (** CAUTION: Non-exhaustive *)
		let neqs = List.filter (fun x -> match x with | BExp.UNIT (_, Op.NE, _) -> true | BExp.UNIT (_, Op.EQ, _)  -> false) eqs in
		List.exists (fun x -> let BExp.UNIT (a, Op.NE, b) = x in prove [] (([],maybe_eqs.eqs_l,[],[]), ([],[BExp.UNIT (a, Op.EQ, b)],[],[]))) neqs 
	(*	List.for_all (fun x -> prove [] (([],maybe_eqs.eqs_l,[],[]), ([],[x],[],[]))) neqs	*)
						
												
	and realize_quantifiers preddefs ((precondition, postcondition) as entailment) = 
				let (pre_exqs, a, b, c) = precondition in
				let (post_exqs, d, e, f) = postcondition in
    		let post_realized_pairs = get_realized_pairs precondition postcondition in
    		let pre_realized_pairs = get_realized_pairs postcondition precondition in
				(** [1;2] [3;4] --> [ (1,3) ; (1,4) ; (2,3) ; (2;4) ] *)
				(** [1] [] --> [ (1,3) ; (1,4) ; (2,3) ; (2;4) ] *)
				pw "Found "; pw (string_of_int (List.length pre_realized_pairs)); pw ",";
				pw (string_of_int (List.length post_realized_pairs)); pw " realized quantifiers variation\n";
    		let all_combinations = cross [(-1, post_realized_pairs) ; (1, pre_realized_pairs)] in
    		if List.length pre_exqs > 0 || List.length post_exqs > 0  then
					begin
						pw "Hence "; pw (string_of_int (List.length all_combinations)); pw " combination(s)\n";
						if all_combinations = [] then
							s_or (substitute_and_prove preddefs (([],a,b,c), (post_exqs,d,e,f))) [[]]
						else
							s_or (substitute_and_prove preddefs (([],a,b,c), (post_exqs,d,e,f))) all_combinations
					end
				else
					prove_rest preddefs entailment
		
	and substitute_and_prove preddefs entailment (vars_with_values : (int * (Var.t * Term.t) list) list) =
			let entailment = local_substitute entailment vars_with_values in
			pprint entailment; pw "     (quantifier substituted)\n";
			prove_rest preddefs entailment
				
				
	and prove_rest preddefs entailment =
				(*let (_, _, pre_pointers, _) = fst entailment in
  			let (_, _, post_pointers,_) = snd entailment in
  			let pointers = (pre_pointers , post_pointers) in  
				let entailment = (Formula.drop_pure pointers (fst entailment), Formula.drop_pure pointers (snd entailment)) in 
  			*)
				let _entailment = drop_matched entailment in  (** Frame Rule *)
  			pprint _entailment; pw " [frame rule]\n";
      		if is_proved _entailment then 
  					begin pw "True\n"; true end  
  				else if is_heap_mismatch _entailment then
  					begin pw "False\n"; false end  
  				else
						nondet_unfold_and_prove preddefs _entailment 
(*        		let unfolded_entailment = strategic_unfold preddefs _entailment in
    				if is_old unfolded_entailment then
    					begin pw "False\n"; false end  
    				else
  						prove preddefs unfolded_entailment	*)
  					

	and nondet_unfold_and_prove preddefs (precondition, postcondition) =
		let (q_a, e_a, pt_a, pr_a) = precondition in
		let (q_b, e_b, pt_b, pr_b) = postcondition in
		let priority_preds exq ptrs preds = (** We filter those predicates for which we have matching pointers *)
			let lst = List.filter 
			(fun pred -> let r =
				match PredicateDefinitions.matched pred preddefs with
				| None -> false
				| Some (q_c, _, pt_c, _) -> 
					List.exists (fun ptr -> List.exists (Pointer.partial_match exq q_c ptr) pt_c) ptrs 
				in let ut = (unfolded_true preddefs pred)	in
				r || ut
			) 
			preds
			in
			pw "["; iterS (Predicate.pprint) "," lst; pw "]\n";
			lst
		in      
		let unfold_and_try (pred_name, args) = 
			push (precondition, postcondition);
			push (drop_the_commons (precondition, postcondition));
			let (_, params, formulas) = List.find (fun (n,_,_) -> n = pred_name) preddefs in
			let r = 
				s_and (fun def -> 
					let def' = Formula.unfold args params def in
					let precondition' : Formula.t = unfold_with_alpha precondition def' (pred_name, args) in
					let eqs_stack = filter_eqs precondition' in
					let r = prove preddefs (precondition', postcondition) in
					maybe_eqs.eqs_l <- (maybe_eqs.eqs_l @ eqs_stack);
					r
					) 
				formulas
			in
			pop (); pop (); r
		in 
		if e_b|==|e_a && pt_a |==| pt_b && pr_a |==| pr_b then
			true
		else if pr_a=[] && pr_b=[] then
			false
		else
			begin
  			pw "strategy in search.. \n";
  			let pr_b' = (priority_preds q_a pt_a pr_b) in
  			let postcondition' = (unfold_a_predicate preddefs) |->> (postcondition, pr_b')  in
  			let pr_a' = (priority_preds q_b pt_b pr_a) in
  			let precondition' = (unfold_a_predicate preddefs) |->> (precondition, pr_a') in
  			pprint (precondition', postcondition'); pw " [unfolded]\n";
  			match check_old (precondition', postcondition') with
    		| Some b -> b
    		| None ->
  			if List.length pr_a' > 0 || List.length pr_b' > 0 then
  				prove preddefs (precondition', postcondition')
  			else
  				s_or unfold_and_try pr_a
			end  
(*
 		| 		_, 		[],   _,    _    -> let pr_b' = (priority_preds q_a pt_a pr_b) in
																		let postcondition' = (unfold_a_predicate preddefs) |->> (postcondition, pr_b') in
																		prove preddefs (precondition, postcondition')		
		|     [], 	_,		_,		_		 -> let pr_a' = (priority_preds q_b pt_b pr_b) in
																		let precondition' = (unfold_a_predicate preddefs) |->> (precondition, pr_a') in
																		prove preddefs (precondition', postcondition)
*)
				
			
	
	let prove_entailment preddefs (precondition, postcondition) =
(*		let init_eqs (_,_,_,preds) = 
			List.map (
				fun (pred_name, args) -> 
					let (_, params, formulas) = List.find (fun (n,_,_) -> n = pred_name) preddefs in
					let r = List.concat (List.map
						(fun def -> 
    					let def' = Formula.unfold args params def in
    					let (_, eqs', _, _) = unfold_with_alpha precondition def' (pred_name, args) in
							eqs') 
    				formulas
					) in
					r) 
			preds >> List.concat
		in 
		let (locations, ls) = get_locs preddefs precondition in
		let lcss = (List.sort_uniq Term.compare (locations @ ls)) in
		pw "\n"; pprint (precondition, postcondition) ; pw "\n\n";
		maybe_eqs.eqs_l <- (init_eqs precondition);   
		pw "eqss: "; iterS BExp.pprint "," maybe_eqs.eqs_l;
		locs.pre <- lcss; 
		locs = {pre = (List.sort_uniq Term.compare ls); post=[]}; 
		pw "************************************************************"; *)
		prove preddefs (precondition, postcondition)
		
	let print (pre, post) = 
		pw "(";
		Formula.print pre;
		pw ",";
		Formula.print post;
		pw ")";;
		
	
end;;

module Program = struct
	type t = Entailment.t list * PredicateDefinitions.t
	
	let prove (entailments, preddefs) = 
		Entailment.prove_entailment preddefs |>>| entailments >> l_and
		
	let print ((es, pds): t) =
		pw "([";
		iterS Entailment.print ";" es;
		pw "],";
		PredicateDefinitions.print pds;
		pw ")\n"
	
		
	let false_entailment = 
		(([],[],[],[]), ([],[],[(Term.NULL,[])],[]))	
end;;

(*
(* TEST *)

(* Step 1 *)
(*
let precondition = ([],[
				BExp.NEQ (Term.VAR "x",Term.VAR "z");
				BExp.NEQ (Term.VAR "w",Term.VAR "z");
				BExp.NEQ (Term.VAR "y",Term.VAR "z")],
				[(Term.VAR "x",[Term.VAR "w";Term.NIL]);
				 (Term.VAR "w",[Term.VAR "y";Term.VAR "x"]);
				 (Term.VAR "y",[Term.VAR "z";Term.VAR "w"])],[])
let postcondition = ([],[],[],[("dll",[Term.VAR "x";Term.VAR "y";Term.NIL;Term.VAR "z"])])	
*)

let predname = "dll";;
let params = ["fr";"bk";"pr";"nx"];;
let body1 = (	[],
							[BExp.EQ (Term.VAR "fr",Term.VAR "nx");BExp.EQ (Term.VAR "bk",Term.VAR "pr")],
							[],
							[]);;
let body2 = (	["u"],
							[BExp.NEQ (Term.VAR "fr",Term.VAR "nx"); BExp.NEQ (Term.VAR "bk",Term.VAR "pr")],
							[(Term.VAR "fr",[Term.VAR "u";Term.VAR "pr"])],
							[("dll",[Term.VAR "u";Term.VAR "bk";Term.VAR "fr";Term.VAR "nx"])]);;

let preddef = (predname, params, [body1; body2]);; 


(* Step 2 *)
let precondition = ([], [BExp.NEQ (Term.VAR "x", Term.VAR "z"); BExp.NEQ (Term.VAR "w", Term.VAR "z"); BExp.NEQ (Term.VAR "y", Term.VAR "z")],
    [(Term.VAR "x", [Term.VAR "w"; Term.NIL]); (Term.VAR "w", [Term.VAR "y"; Term.VAR "x"]); (Term.VAR "y", [Term.VAR "z"; Term.VAR "w"])], 
    []);;
let postcondition = 
   (["u"], [BExp.NEQ (Term.VAR "x", Term.VAR "z"); BExp.NEQ (Term.VAR "y", Term.NIL)], 
    [(Term.VAR "x", [Term.VAR "u"; Term.NIL])],
    [("dll", [Term.VAR "x"; Term.VAR "y"; Term.NIL; Term.VAR "z"]); ("dll", [Term.VAR "u"; Term.VAR "y"; Term.VAR "x"; Term.VAR "z"])]);;

let entailment = (precondition, postcondition);;
let _entailment = Entailment.normalize entailment ;;

(* let __entailment = Entailment.realize_existential_quantifiers _entailment ;; *)
let (_, _, pre_ptrs, _) = precondition ;;
let (exqs, es, post_pointers, ps) = postcondition ;;
let exq::_ = exqs;;
let container_pointers = List.filter (Pointer.contained_in exq) post_pointers;;
let pre_pointers = pre_ptrs;;
let pointer::_ = container_pointers;;
let ptr1::ptr2::ptr3::_ = pre_pointers;;

let (location_b, elements_b) = pointer;;
let (location_a, elements_a) = ptr1;;

let f_match = fun a b -> 	if a = b then 
																None 
															else if b <> Term.NIL && Term.decode b |<- exqs then
																Some (Term.find b exqs, a)					(** (Quantifier Term, Actual value) *)
															else
																None;;
																
let location_match = f_match location_a location_b;;
let elements_match = List.map2 f_match elements_a elements_b ;;
let valid_matches = location_match :: elements_match >> valids_only;;

(*
Pointer.partial_match exqs pointer ptr1;;
Pointer.partial_match exqs pointer ptr2;;
Pointer.partial_match exqs pointer ptr3;;
*)

let matched_pairs = (Entailment.partial_matches exqs pre_pointers) |>>| container_pointers >> List.concat;;
let (qvar, value)::_ = List.filter (fun (a,b) -> Term.decode a = exq) matched_pairs;;
(*
(Entailment.partial_matches exqs pre_pointers) |>>| container_pointers;;


let ___entailment = Entailment.drop_matched __entailment;;
let ____entailment = (Formula.filter_trivial (fst ___entailment), Formula.filter_trivial (snd ___entailment)) ;;
		
Entailment.is_proved ____entailment;;

let unfolded_entailment = Entailment.unfold [preddef] ____entailment;;
*)

*)
