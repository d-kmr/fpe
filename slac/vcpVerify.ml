
open VcpTranslate
open VcpBase
open Ftools
(* open VcpEntailment *)

let linear = ref false
let count = ref 0

(*
let check_immidiate_contradiction eqfs locs =
  let rec check_all maps = function
    | [] -> false
    | x::xs -> 
      match x with
      | BExp.UNIT (Term.EXP (Exp.CONST y), Op.EQ, Term.EXP (Exp.CONST z)) when y <> z -> true
      | BExp.UNIT (Term.EXP (Exp.VAR y), Op.NE, Term.NULL) -> not (Var.toStr y |<- locs) 
      | BExp.UNIT (Term.EXP (Exp.CONST y), Op.LE, Term.EXP (Exp.CONST z)) when y > z || y = z -> true
      | BExp.UNIT (Term.NULL, Op.NE, Term.EXP (Exp.CONST 0)) -> true 
      | BExp.UNIT (x, Op.NE, y) -> x = y
      | BExp.OP (y, Op.OR, z) -> (check_all maps [y]) && (check_all maps [z])
      | BExp.OP (y, Op.AND, z) -> check_all maps [y; z]
      | _ -> check_all maps xs
  in
  let v = check_all [] eqfs in
  v

let ucheck_c verbose (_, eqfs, ptr_list, _) =  
  (** a=b & A is equivalent to A[a:=b]. So *)
  let eqfs' = BExp.substitutes eqfs eqfs in
  let ptr_list' = Pointer.substitutes ptr_list eqfs in
  let rec neq_f = function
      [] -> []
    | x::xs ->
      match x with
        BExp.UNIT(pt, Op.NE, Term.NULL) -> pt :: (neq_f xs)
      | _ -> neq_f xs
  in
  let is_any_not_null_invalid () =
    let neqs = neq_f eqfs in
    match List.filter (fun x ->
        let vx = Term.decode x in
        Var.is_ptr vx && (not (Var.is_struct vx)) && 
        not (List.exists (fun y -> match y with BExp.UNIT(y',Op.MAPSTO,_) -> x=y' | _ -> false ) eqfs)) neqs with
      x::_ ->
      if verbose then begin Term.pprint x; pn " no ref" end;
      true
    | [] ->
      match List.filter (fun x ->
          let vx = Term.decode x in
          Var.is_ptr vx && (not (Var.is_struct vx)) &&
          not (List.exists (fun (y,_) -> y = x ) ptr_list)) neqs with
        x::_ ->
        if verbose then begin 
          Term.pprint x;
          pn " no ptr"
        end;
        true
      | _ -> false
  in
  let locs = Var.toStr |>>| (Term.decode |>>| (fst |>>| ptr_list')) in
  let cic = check_immidiate_contradiction eqfs' locs in
  if cic then
    begin
      if verbose then
        pn "Immidiate contradiction";
      true
    end
  else
      let is_pt_null = (List.exists (fun (pt,_) -> (pt = Term.NULL) || (pt = Term.EXP (Exp.CONST  0))) ptr_list') in
      if is_pt_null then
        begin
          if verbose then
            pn "Some pointer is null";
          true
        end
      else
        let ianni = is_any_not_null_invalid () in
        if ianni then
          begin
            if verbose then
              pn "Some not null is invalid";
            true
          end
        else
            false

let check_c verbose form =
  List.filter (fun f -> not (ucheck_c verbose f)) form 
  
let in_dim dim indices = true

let update_vars vars var exp loc =
  let v = fst var in
  if not (List.exists (fun (w, _) -> w = v) vars) && (exp = Term.NULL || exp = Term.EXP Exp.NOTHING) then
    var::vars
  else if (Bytes.get v 0) = '.' then
    let attrs = Term.infer_attributes vars loc exp in
    (v, attrs)::vars
  else
    vars



let rec validate ((pre, program, post) : Formula.t * Block.t * Formula.t) (fv:int) ((procs, vars, structures) as packs) : (int * (Formula.t * Formula.t)) list =  
   (* Formula.pprint pre; pn ""; 
      Block.pprint 0 program; pn ""; *)
  let n1 = List.length (fst pre) in
  let pre = uniq (fst pre), snd pre in
  let n2 = List.length (fst pre) in
  prerr_int n1;
  prerr_string " -> ";
  prerr_int n2;
  prerr_endline "";
  Formula.pprint pre; pn "\n";
  let pre = check_c false (fst pre), snd pre in
  if (fst pre) = [] then
    begin
      (* pn " - X"; *)
      []
    end
  else 
    begin
      (* pn " - OK"; *)
      (*  iterS Var.pprint "," vars; pn ""; *)
    (* Formula.pprint pre; pn ""; *)  
    match program with
    | Block.SKIP ->
      (* count.contents <- !count + 1;
         prerr_int !count; prerr_endline " ."; *) 
      [(fv, (pre, post))]              
    | Block.ASSERT (formula, pr, _) ->
      (* prerr_string "B"; *)
      (fv, (pre, formula)) :: validate (formula, pr, post) fv packs
        
    | Block.ASSIGN (var, exp, program, l) ->
      (* prerr_string "C"; *) 
      let (vars : Var.t list) = update_vars vars var exp l in
      
      (** Skip unitialized declaration *)
      (* if exp = Term.EXP Exp.NOTHING then
        begin
         
          validate (pre, program, post) fv (procs, var::vars, structures)
            end
         else *)
        (* (** Not more necessary now *)        
           let (_, eqs, _, _) = pre in
           if exp = Term.EXP (Exp.VAR ("$ret", [])) && Var.is_ptr var && List.exists (fun x ->
            match x with
              BExp.UNIT (a, Op.EQ, b) -> Term.toStr a = "$ret" || Term.toStr b = "$ret"
            | _ -> false
          ) eqs then
          let pro, fv' = 
            if Var.is_struct var then
              let struct_name = Var.get_struct_name var in
              let (_, my_struct) = List.find (fun (a, b) -> a = struct_name) structures in
              let my_struct = (fun (a, b) -> (Bytes.concat "." a, b)) |>>| my_struct in
              Block.PARALLEL (Block.ASSIGN(var, Term.NULL, Block.SKIP, l) , Block.CONS(Exp.encode var, my_struct, Block.SKIP, l), program, l), fv
            else
              let fv' = Formula.fresh_variable fv in
              let vfv' = (string_of_int fv', Var.get_attributes var) in
              Block.PARALLEL (Block.ASSIGN(var, Term.NULL, Block.SKIP, l) , Block.MAPS(var, vfv', Block.SKIP, l), program, l), fv'
          in
          validate (pre, pro, post) fv' (procs, vars, structures)
          else *)
          begin
            (** x=exp[x:=x'] & (PI & SIGMA)[x:=x'] *)
            let exps = (fun _ -> exp) |>>| (fst pre) in
            let (pre', fv') = Formula.assign vars pre var exps fv l in
            (* let is_new pt =  
               List.exists (fun x -> Formula.(===) eqs pt x) (!Formula.new_ptr) 
               in *)
            if Var.toStr var = "$ret" then
              begin
                List.iter (fun (_, eqs, ptr_list, _) ->
                (*Formula.pprint pre; pn "";*)
                (* pn (Locs.toLine l);
                   Formula.pprint pre'; pn "\n"; *) 
                let allocated_memory = (fun (pt, _) -> let vpt = Term.decode pt in Var.is_struct vpt && Var.is_ptr vpt && (not (Var.is_param vpt)) ) |>- ptr_list in
                (* iterS Pointer.pprint "--" allocated_memory; pn "\n"; *)
                let non_return_memory = List.filter (fun (pt, _) -> not (Formula.(===) eqs exp pt) ) allocated_memory in
                (* let extra_memory = List.filter (fun (pt, _) -> is_new pt) non_return_memory in *)
                if List.length non_return_memory > 0 then
                  begin
                    (* Formula.pprint pre'; pn ""; *)
                    List.iter (fun ptr ->
                        match Formula.get_real_var eqs (fst ptr) with
                          Some (sptr) -> warn ("Memory Leak (left over) by " ^ sptr) l () (* "ML & " *)
                        | None -> ()
                      ) non_return_memory
                  
                  end
                ) (fst pre')
              end;
            (* pw "ASSIGN:"; (* Formula.pprint pre'; pn ""; *) *) 
            validate (pre', program, post) fv' (procs, vars, structures)
          end
    | Block.CONS (e_v, ts, pr, l) ->                                            (** v is expected to be properly typed if not already in vars *)
      (* prerr_string "D"; prerr_string (Locs.toLine l); *)
      let v       =
        match e_v with
          Exp.VAR v -> v
        | Exp.BINOP(Exp.VAR v, _, _) -> v
        | _ -> raise SError
      in
      let sv      = fst v in   (** name of variable *)
      let vars, e_v =
        if not (List.exists (fun (w, _) -> w = sv) vars) then
          v::vars, e_v           (** if it is new then add to vars *)
        else
          vars, Exp.be_typed vars l e_v 
      in
            
      if Var.is_struct v || Var.is_array v then                                                   (** Redundant: already checked by compiler. *)
        begin
          let fv'     = Formula.fresh_variable fv in
          let v_fv    = Var.toVar (Formula.i_to_v fv') in
          let t_fv    = Term.encode (Var.set_attributes v_fv (Var.get_attributes v)) in
          let (_, eqs, ptrs, _) = List.hd (fst pre) in
          let v       = 
            if List.exists (fun x -> match x with BExp.UNIT (v, Op.EQ, _) -> Term.toStr v = "$return" | _ -> false) eqs then
              begin
                (fst v, (fun x -> match x with Var.PARAM -> false | _ -> true) |>- (snd v))
              end
            else
              begin
                v
              end
          in
          let t_v     = Term.encode v in
          let pre'    = Formula.substitute t_v t_fv pre l in 
          let pre''   = Formula.add_to_spatial pre' (t_v, ts) in                  (** CAUTION: dummy field is used *)
          let pre''' = Formula.is_memory_leak eqs ptrs t_v pre'' pre l in
          validate (pre''', pr, post) fv' (procs, vars, structures)
        end
      else
        (* let _ = warn (" TYPE MISMATCH: " ^ (Var.toStr v) ^ " is not a struct type") l () in *)
        validate (pre, pr, post) fv (procs, vars, structures)
    | Block.LOOKUP (v, ((Term.EXP (Exp.VAR ptv)) as pt), "*", pr, l) ->
      (* prerr_string "E"; prerr_string (Locs.toLine l); *)
      let pres_progs =
        (fun (exqs, eqs, ptrs, preds) -> 
           begin
             let ref = (fun x ->                                                     (** find what x points to... *)
                 match x with
                 | BExp.UNIT (y, Op.MAPSTO, z) when Formula.(===) eqs y pt -> true 
                 | _ -> false ) |>- eqs 
             in
             begin
               match ref with 
               | BExp.UNIT (_, _, exp) :: [] ->  
                 (exqs, eqs, ptrs, preds), Block.ASSIGN (v, exp, pr, l)
               (** {A & pt=>z} v = z {B} |- {A & pt=>z} v = *pt {B} *)
               | _ ->
                 (exqs, (BExp.UNIT (Term.encode v, Op.MAPSTO, pt))::eqs, ptrs, preds), pr
             end
           end
        ) |>>| (fst pre)
      in
      let (pres, progs) = List.split pres_progs in
      validate ((pres, snd pre), List.hd progs, post) fv packs
    | Block.LOOKUP (v, pt, "*", pr, l) ->
      (* prerr_string "F"; prerr_string (Locs.toLine l); *)
      
      if Var.is_array (Term.decode pt) then 
        let pres =
          (* (fun p' ->process_array pt fv "*" (fun x -> [], [p']) (fun x -> []) p') |>>| pre in *)
          (fun (a,b,c,d) ->
             let mt = (fun (ptr, ds) -> Term.toStr ptr = Term.toStr pt) |>- c in
             let new_pre, value, fv = 
               match mt with
                 [(_, (_,value)::[])] -> [], value, fv
               | _ ->
                 (*let ix'   = Formula.fresh_variable fv in
                 let i_s   = Formula.i_to_v ix' in
                 let vx'   = Var.set_attributes (Var.toVar i_s) [] in
                 Term.encode vx', ix'
                 *)
                 begin
                   let arr, index =
                     match pt with
                       Term.EXP (Exp.VAR x) -> Exp.VAR x, Exp.CONST 0
                     | Term.EXP (Exp.BINOP (x, Op.ADD, y)) -> x, y
                     | _ -> Exp.NOTHING, Exp.CONST 0
                   in
                   let fv    = Formula.fresh_variable fv in
                   let i_s   = Formula.i_to_v fv in
                   let tx'   = Term.encode (Var.set_attributes (Var.toVar i_s) []) in
                   (** Check if there is an Array with the same head *)
                   let matched, unmatched = List.partition (fun (s_pred, ts) -> s_pred = "Array" && Term.decode (List.hd ts) = Exp.decode arr) d in
                   let new_pre =
                     (fun (_, ts) ->
                        let t_array = List.nth ts 0 in (* y *)
                        let e_array = match t_array with Term.NULL -> Exp.NOTHING | Term.EXP y'' -> y'' in
                        let offset = match e_array with
                            Exp.BINOP (_, Op.ADD, y) -> y
                          | _ -> Exp.CONST 0
                        in
                        
                        let len = match List.nth ts 1 with Term.EXP l -> l | _ -> Exp.NOTHING in (* n *)
                        let rest = (fun (a, b) -> b != ts) |>- matched in  (* other array segments *)
                        (** Unfolding current array segment *)
                        let pred1 = ("Array", [Term.EXP e_array; (Term.EXP (Exp.eval (Exp.BINOP (index, Op.SUB, offset))))]) in
                        let new_arr = Term.EXP (Exp.eval (Exp.BINOP (arr, Op.ADD, Exp.BINOP (index, Op.ADD, Exp.CONST 1)))) in
                        let new_len = Term.EXP (Exp.eval (Exp.BINOP (len, Op.SUB, Exp.BINOP (Exp.BINOP(index, Op.SUB, offset), Op.ADD, Exp.CONST 1)))) in
                        let pred2 = ("Array", [new_arr; new_len]) in
                        let new_loc = Term.EXP (Exp.eval (Exp.BINOP (arr, Op.ADD, index))) in
                        let pure = [
                          BExp.UNIT (Term.EXP index, Op.LE, Term.EXP len);
                          BExp.UNIT (Term.EXP offset, Op.LE, Term.EXP (Exp.eval (Exp.BINOP (index, Op.ADD, Exp.CONST 1))))
                        ] in
                        (* let new_pre = (a, pure @ b, (new_loc, [i, t])::c, pred1::pred2::(rest @ unmatched)) in *)
                        let pre' =  (i_s::a, pure @ b, (new_loc, ["*", tx'])::c, pred1::pred2::(rest @ unmatched)) in
                        pre'
                        (*validate ([new_pre], pr, post) fv packs, pre' *)
                     )
                     |>>| matched
                   in
                   (*let post' = (fun (_, p) -> p) |>>| entls_pre' in *)
                   (* let pres : (int * (Formula.t * Formula.t)) = (fv, (pre, pre')) in
                  (* let entls = List.concat (fst |>>| entls_pre') in *)
                      pres *)
                   new_pre, tx', fv
                 end                 
             in
             (* validate (pre', pr, post) fv' packs *) 
             new_pre, value, fv
          ) |>>| (fst pre) in
        let new_pre = List.concat ((fun (a,_,_) -> a) |>>| pres) in
        let value = List.hd ((fun (_,a,_) -> a) |>>| pres) in
        let entl = 
          if new_pre = [] then
            let v_t = (fun _ -> value) |>>| (fst pre) in
            let (pre', fv') = Formula.assign vars pre v v_t fv l in
            validate (pre', pr, post) fv packs 
          else
            let v_t = (fun _ -> value) |>>| new_pre in
            let (new_pre', fv') = Formula.assign vars (new_pre, snd pre) v v_t fv l in            
            (fv, (pre, (new_pre, snd pre))) :: validate (new_pre', pr, post) fv packs
        in
        entl 
      else
        validate (pre, pr, post) fv packs
    | Block.LOOKUP (v, pt, i, pr, l) ->                                        (** {A * pt->(i:v_t)} v = pt->i {B} |- {A * pt->(i:v_t)} v = v_t {B} *)
      (* prerr_string "G"; prerr_string (Locs.toLine l); *)
      (* let pt = Term.be_typed vars l pt in *)
      let v_t = Formula.get_from pre pt i l in
      let (pre', fv') = Formula.assign vars pre v v_t fv l in
      validate (pre', pr, post) fv' packs
    | Block.MUTATION ((Term.EXP (Exp.VAR ptv)) as pt, "*", t, pr, l) ->        (** {A & pt=>z} z = t {B} |- {A & pt=>z} *pt = t {B} *)
      (* prerr_string "H"; prerr_string (Locs.toLine l); *)
      let (_, eqs, _, _) = List.hd (fst pre) in
      let ref = (fun x ->
        match x with
        | BExp.UNIT (y, Op.MAPSTO, z) when y = pt -> true 
        | _ -> false ) |>- eqs 
      in
      begin
      match ref with
      | BExp.UNIT (_, Op.MAPSTO, Term.EXP (Exp.VAR exp)) :: [] -> 
        validate (pre, Block.ASSIGN (exp, t, pr, l), post) fv packs
      | _ -> 
        validate (pre, pr, post) fv packs
      end
      
    | Block.MUTATION (pt, i, t, pr, l) ->
       let intv = snd pre in
       let pre = fst pre in
      if Var.is_array (Term.decode pt) then
        begin 
          let pres =
            (fun (a,b,c,d) ->
              (** Check if it is already processed *)
              let mt, rest = List.partition (fun (ptr, ds) ->
                  Term.toStr ptr = Term.toStr pt) c in
              match mt with
                [(ptr, _)] ->
                (** If already processed, no A' and C is modified heap *)
                let c' = (pt, [("*", t)]) :: rest in
                [], [(a,b,c',d)]
              | _ ->
                begin
                  let arr, index =
                    match pt with
                      Term.EXP (Exp.VAR x) -> Exp.VAR x, Exp.CONST 0
                    | Term.EXP (Exp.BINOP (x, Op.ADD, y)) -> x, y
                    | _ -> Exp.NOTHING, Exp.CONST 0
                  in
                  let fv    = Formula.fresh_variable fv in
                  let i_s   = Formula.i_to_v fv in
                  let tx'   = Term.encode (Var.set_attributes (Var.toVar i_s) []) in
                  (** Check if there is an Array with the same head *)
                  let matched, unmatched = List.partition (fun (s_pred, ts) -> s_pred = "Array" && Term.decode (List.hd ts) = Exp.decode arr) d in
                  let entls_pre' =
                    (fun (_, ts) ->
                       let t_array = List.nth ts 0 in (* y *)
                       let e_array = match t_array with Term.NULL -> Exp.NOTHING | Term.EXP y'' -> y'' in
                       let offset = match e_array with
                           Exp.BINOP (_, Op.ADD, y) -> y
                         | _ -> Exp.CONST 0
                       in
                       
                       let len = match List.nth ts 1 with Term.EXP l -> l | _ -> Exp.NOTHING in (* n *)
                       let rest = (fun (a, b) -> b != ts) |>- matched in  (* other array segments *)
                       (** Unfolding current array segment *)
                       let pred1 = ("Array", [Term.EXP e_array; Term.EXP (Exp.eval (Exp.BINOP (index, Op.SUB, offset)))]) in
                       let new_arr = Term.EXP (Exp.eval (Exp.BINOP (arr, Op.ADD, Exp.BINOP (index, Op.ADD, Exp.CONST 1)))) in
                       let new_len = Term.EXP (Exp.eval (Exp.BINOP (len, Op.SUB, Exp.BINOP (Exp.BINOP(index, Op.SUB, offset), Op.ADD, Exp.CONST 1)))) in
                       let pred2 = ("Array", [new_arr; new_len]) in
                       let new_loc = Term.EXP (Exp.eval (Exp.BINOP (arr, Op.ADD, index))) in
                       let pure = [
                         BExp.UNIT (Term.EXP index, Op.LE, Term.EXP (Exp.eval( Exp.BINOP (Exp.BINOP(len, Op.ADD, offset), Op.SUB, Exp.CONST 1))));
                         BExp.UNIT (Term.EXP offset, Op.LE, Term.EXP (Exp.eval (Exp.BINOP (index, Op.ADD, Exp.CONST 1))))
                       ] in
                       let new_pre = (a, pure @ b, (new_loc, [i, t])::c, pred1::pred2::(rest @ unmatched)) in
                       let pre' =  (i_s::a, pure @ b, (new_loc, [i, tx'])::c, pred1::pred2::(rest @ unmatched)) in
                       pre', new_pre
                       (*validate ([new_pre], pr, post) fv packs, pre' *)
                    )
                    |>>| matched
                  in
                  let pre' = fst |>>| entls_pre' in
                  let new_pre = snd |>>| entls_pre' in
                  (*let post' = (fun (_, p) -> p) |>>| entls_pre' in *)
                  (* let pres : (int * (Formula.t * Formula.t)) = (fv, (pre, pre')) in
                  (* let entls = List.concat (fst |>>| entls_pre') in *)
                     pres *)
                  pre', new_pre
                end
            ) |>>| pre in
          let pre' = (List.concat (fst |>>| pres), intv) in
          let new_pre = (List.concat (snd |>>| pres), intv) in
          let (entls : (int * (Formula.t * Formula.t)) list) = validate (new_pre, pr, post) fv packs in
          if fst pre' = [] then
            entls
          else
            (fv, ((pre, intv), pre'))::entls
          
            (* match matched with
              [] ->
              validate (pre, pr, post) fv packs
            | [(_, ts)] ->
              let e_array = List.nth ts 0 in
              let len = List.nth ts 1 in
              let pred1 = ("Array", [e_array; Term.EXP index]) in
              let len' = Exp.VAR (Term.decode len) in
              let new_arr = Term.EXP (Exp.BINOP (arr, Op.ADD, Exp.BINOP (index, Op.ADD, Exp.CONST 1))) in
              let new_len = Term.EXP (Exp.BINOP (len', Op.SUB, Exp.BINOP (index, Op.ADD, Exp.CONST 1))) in
              let pred2 = ("Array", [new_arr; new_len]) in
              let new_loc = Term.EXP (Exp.BINOP (arr, Op.ADD, index)) in
              let new_pre = [(a, b, (new_loc, [i, t])::c, pred1::pred2::unmatched)] in
              let pure = [BExp.UNIT (Term.EXP index, Op.LE, Term.EXP len'); BExp.UNIT (Term.EXP (Exp.CONST 0), Op.LE, Term.EXP (Exp.BINOP (index, Op.ADD, Exp.CONST 1)))] in
              let pre' = [(i_s::a, pure @ b, (new_loc, [i, tx'])::c, pred1::pred2::unmatched)] in
              let entls = validate (new_pre, pr, post) fv packs in
              (0, (pre, pre'))::entls
               | _ -> *)
        end
      else
        begin
      let pt = Term.be_typed vars l pt in
      let ts = (fun _ -> t) |>>| pre in
      let pre' = (Formula.set_to (pre,intv) pt i ts l) in
      (* pw "MUTATION:"; (* Formula.pprint pre'; pn ""; *) *)
      validate (pre', pr, post) fv packs
        end
    | Block.DISPOSE (pt, pr, l) -> 
      (* prerr_string "J"; prerr_string (Locs.toLine l); *)
      let (_, eqs, _, _) = List.hd (fst pre) in
      Formula.new_ptr.contents <- (List.filter (fun x -> not (Formula.(===) eqs x pt)) !Formula.new_ptr);
      let pre' = Formula.delete_from pre pt l in
      (* pw "DISPOSE:"; (* Formula.pprint pre'; pn ""; *) *)
      validate (pre', pr, post) fv packs
    | Block.IF (e, p1, p2, pr, l) ->
      (* prerr_string "*"; *)
      let pre1 = Formula.add_to_formula pre e in
      let pre2 = Formula.add_to_formula pre (BExp.complement e) in 
      (* pw "IF:"; (* Formula.pprint pre1; pw " AND"; Formula.pprint pre2; pn ""; *) *)
      (* List.append (validate (pre1, Block.compose pr p1, post) fv packs)  (validate (pre2, Block.compose pr p2, post) fv packs) *)
      let p1' = Block.compose pr p1 in
      let p2' = Block.compose pr p2 in
      let b1  = (check_c false (fst pre1)) = [] in
      let b2  = (check_c false (fst pre2)) = [] in
      if !linear then
        if b1 && b2 then
          raise (StError ("IF problem"))
        else if b1 then
          begin
            validate (pre2, p2', post) fv packs
          end
        else
          begin
            (*          prerr_endline "X";*)
            validate (pre1, p1', post) fv packs
          end
      else
        let entl1 : (int * (Formula.t * Formula.t)) list = validate (pre1, p1, post) fv packs in
        let entl2 = validate (pre2, p2, post) fv packs in
        let entl1', entl1'' = List.partition (fun (_, (_, post)) -> post != Formula.trueempty) entl1 in
        let entl2', entl2'' = List.partition (fun (_, (_, post)) -> post != Formula.trueempty) entl2 in
        let post1' = List.concat ((fun (_, (pre, _)) -> fst pre) |>>| entl1'') in
        let post2' = List.concat ((fun (_, (pre, _)) -> fst pre) |>>| entl2'') in
        let entl12 = validate ((post1' @ post2',[]), pr, post) fv packs in 
        entl1' @ entl2' @ entl12
    | Block.MAPS (_from, _to, body, l) ->
      (* prerr_string "L"; prerr_string (Locs.toLine l); *)
      let form = (fun (a, eqs, b, c) -> 
          (** discard old reference of _from *)
          let (_, rest) = List.partition (fun x -> 
              match x with 
              | BExp.UNIT (y, Op.MAPSTO, _) -> y = (Term.encode _from) 
              | _ -> false) eqs 
          in  
          let exp = BExp.UNIT (Term.encode _from, Op.MAPSTO, Term.encode _to) in
          let eqs' = Formula.is_memory_leak eqs b (Term.encode _from) (exp::rest) rest l in
          (a, eqs', b, c)
        ) |>>| (fst pre) in
      validate ((form, snd pre), body, post) fv packs
    | Block.PARALLEL (pr1, pr2, pr, l) ->
      (* prerr_string "M"; prerr_string (Locs.toLine l); *)
      (* prerr_string "."; *) 
      List.append (validate (pre, Block.compose pr pr1, post) fv packs)  (validate (pre, Block.compose pr pr2, post) fv packs)
    | Block.PROCCALL (str, args, body, l) ->
      begin
        let (_, eqs, ptrs, _) = List.hd (fst pre) in 
        List.iter (fun x ->
            let x = Term.be_typed vars l x in
            if Formula.(===) eqs x Term.NULL then
              match Formula.get_real_var eqs x with
              | None ->
                (* warn ((Term.toStr x) ^ " is a Null Argument") l*) () 
              | Some s ->
                warn (s ^ " is a Null Argument") l ()
          ) args; 
        match body with
          Block.ASSIGN (v1, e1, b1, l1) when Term.toStr e1 = "$ret" -> 
          let (is_ptr, is_struct, type_name) = 
            try
              let ((name, param_statements, _), pre1, post1) = 
                List.find (fun ((name, _, _), _, _) -> Var.toStr name = str) procs in
              (Var.is_ptr name, Var.is_struct name, Var.get_struct_name name )
            with
              _ ->
              (Var.is_ptr v1, Var.is_struct v1, Var.get_struct_name v1)
          in
          begin
            match is_ptr, is_struct with
              true, true ->
              if Block.contains str "new" || Block.contains str "alloc" then
                let f_struct = List.filter (fun (n, _) -> n = type_name) (!Block.structures) in
                let body =
                  try
                    Block.PARALLEL(
                      Block.ASSIGN (v1, Term.NULL, Block.SKIP, l1),
                      Block.CONS (Exp.VAR v1, (fun (ns, e) -> (Bytes.concat "." ns, e)) |>>| (snd (List.hd f_struct)), Block.SKIP, l1),
                      b1,
                      l)
                  with
                    _ -> raise (StError("verify - Block.ASSIGN - true,true\n"))
                in
                (* pn "Proc to Parallel ";
                Var.pprint v1; pn "";
                Block.pprint 0 body; *)
                validate (pre, body, post) fv packs
               else
                 let fit = List.filter (fun (x, _) -> Var.get_attributes (Term.decode x) = Var.get_attributes v1) ptrs in
                 begin
                   match fit with
                     [] -> validate (pre, body, post) fv packs
                   | (fit1, _) :: _ -> validate (pre, Block.ASSIGN (v1, fit1, b1, l1), post) fv packs
                 end
            | true, false ->
              let nv = newvar () in
              let attr = Var.get_attributes v1 in
              let body =
                if !linear then
                  Block.MAPS (v1, (nv, attr), b1, l) 
                else
                  Block.PARALLEL(
                    Block.ASSIGN (v1, Term.NULL, Block.SKIP, l),
                    Block.MAPS (v1, (nv, attr), Block.SKIP, l),
                    b1,
                    l)
              in validate (pre, body, post) fv packs 
            | false, true ->
              let (_, fields) = List.find (fun (n, _) -> n = type_name) (!Block.structures) in
              let body = Block.CONS (Exp.VAR v1, (fun (ns, e) -> (Bytes.concat "." ns, e)) |>>| fields, b1, l) in
              validate (pre, body, post) fv packs
            | false, false ->
              let nv = newvar () in
              let attr = Var.get_attributes v1 in
              let body = Block.ASSIGN (v1, Term.encode (nv, attr), b1, l) in
              validate (pre, body, post) fv packs
          end
        | _ -> validate (pre, body, post) fv packs
      end
(*    | Block.PROCCALL (str, args, body, l) -> 
      begin
      try
        begin
          (** Check if the procedure exists in current module *)
          let ((name, param_statements, _), pre1, post1) = 
            List.find (fun ((name, _, _), _, _) -> Var.toStr name = str) procs in
          pw "#"; Var.pprint name;
          (** Convert all the parameter to Var *)
          let params = Procedure.to_var |>>| param_statements in
          (** Filter the valid parameters *)
          let params = List.filter (fun x -> Bytes.length (Var.toStr x) > 0) params in
          (*    let block' = List.fold_left2 (fun b p a -> Block.ASSIGN (p, a, b, l)) block params args in *)
          (** If number of parameters and arguments are the same *)
          if List.length params = List.length args then
            let pre1' = List.fold_left2 (fun (f : Formula.t) (p : Var.t) (a : Term.t) -> Formula.substitute (Term.encode p) a f l) pre1 params args in
            let post1' = List.fold_left2 (fun f p a -> Formula.substitute (Term.encode p) a f l) post1 params args in
            (* pw "PROCCALL:"; (* Formula.pprint pre1'; pw " AND"; Formula.pprint post1'; pn ""; *) *)
            let ent = (pre, pre1') in
            let ents = validate (post1', body, post) fv packs in
            (fv, ent) :: ents
          else
            begin
              (*              pw name; pi (List.length params); pw ""; iterS Var.pprint "," params; pw "::"; iterS Term.pprint "," args; pn ""; *)
              validate (pre, body, post) fv packs
            end
        end
      with
      | Not_found -> 
        begin
          (* pw "PROC "; pw str; pw "NOT FOUND @"; pn (Locs.toStr l); *)
        (*  let (exq, eqs, ptrs, preds) = pre in
          let eqs = (fun x ->
              match x with
                BExp.UNIT (a, Op.EQ, b) -> not (Term.toStr a = "$ret" || Term.toStr b = "$ret")
              | _ -> true 
            ) |>- eqs in *)
          validate (pre, body, post) fv packs
        end
      end *)
    | Block.WHILE (b, block, inv, body, l) ->
      (* prerr_string "O"; prerr_string (Locs.toLine l); *)
      if inv = ([([],[],[],[])], []) then 
        validate (pre, Block.IF (b, block, Block.SKIP, body, l), post) fv packs
      else
        let f, f' = List.split ((fun (x,y,z,w) -> (x, b::y, z, w), (x, (BExp.complement b)::y, z, w)) |>>| (fst inv)) in
        let ent1 : Formula.t * Formula.t = (pre, (f, snd inv)) in
        let entl1 = validate ((f, snd inv), block, inv) fv packs in
        let entl2 = validate ((f', snd inv), body, post) fv packs in
        (fv, ent1)::(entl1 @ entl2)
    | Block.ARRAY (a, b, tl, body, _) ->
      (* prerr_string "P"; *)
      (*    let new_pred = (a, [Term.zero; b; Term.EXP Exp.NOTHING]) in *)
      let pre' = 
        if tl = [] then
          let array_pred = ("Array", [Term.encode a; b]) in
          (fun (exqs, eqs, c, pred) -> (exqs, eqs, c, array_pred::pred)) |>>| (fst pre)
        else
          (fun (exqs, eqs, c, pred) -> 
             let pointers = List.mapi (fun i x -> (Term.EXP (Exp.BINOP (Exp.VAR a, Op.ADD, Exp.CONST i)), [("*", x)]) ) tl in
             (exqs, eqs, pointers @ c, pred)
          ) |>>| (fst pre)
      in
      validate ((pre', snd pre), body, post) fv (procs, a::vars, structures)
    end;;



let rec classify_params (refs : Block.t list) unrefs = function
    Block.SKIP -> refs, unrefs
  | Block.ASSIGN (_, _, pr, _) -> classify_params refs unrefs pr
  | Block.CONS (e_v, _, pr, _) ->
    let refs, unrefs = classify_params refs unrefs pr in
    let matched, unmatched = List.partition (fun x -> Exp.VAR (Procedure.to_var x) = e_v) refs in
    unmatched, matched @ unrefs
  | Block.LOOKUP (v, _, _, pr, _) ->
    let matched, unmatched = List.partition (fun x -> (Procedure.to_var x) = v) unrefs in
    classify_params (matched @ refs) unmatched pr
  | Block.MUTATION (pt, _, _, pr, _) 
  | Block.DISPOSE (pt, pr, _) ->
    let matched, unmatched = List.partition (fun x -> (Procedure.to_var x) = Term.decode pt) unrefs in
    classify_params (matched @ refs) unmatched pr
  | Block.IF (_, p1, p2, pr, _) ->
    let refs1, unrefs1 = classify_params refs unrefs p1 in
    let refs2, unrefs2 = classify_params refs1 unrefs1 p2 in
    classify_params refs2 unrefs2 pr 
  | Block.MAPS (_, _, pr, _) -> classify_params refs unrefs pr
  | Block.PARALLEL (pr1, pr2, pr, _) ->
    let refs1, unrefs1 = classify_params refs unrefs pr1 in
    let refs2, unrefs2 = classify_params refs1 unrefs1 pr2 in
    classify_params refs2 unrefs2 pr
  | Block.PROCCALL (_, params, pr, _) ->
    classify_params refs unrefs pr
  | Block.WHILE (_, p1, _, pr, _) ->
    let refs1, unrefs1 = classify_params refs unrefs p1 in
    classify_params refs1 unrefs1 pr
  | Block.ARRAY (_, _, _, pr, _) 
  | Block.ASSERT (_, pr, _) -> classify_params refs unrefs pr
  



let filter_global (a, eqs, b, c) fvs = 
  let eqs' = (fun x ->
      match x with
        BExp.UNIT (t1, _, t2) -> ((Term.toStr t1) |<- fvs) || ((Term.toStr t1) |<- fvs) 
      | _ -> false
    ) |>- eqs in
  (a, eqs', b, c)

let get_null_parameter loc structures body param_statement =
  let param = Procedure.to_var param_statement in
  Block.ASSIGN(param, Term.NULL, body, loc) 

let get_nondeterministic_parameter loc structures (body, i) param_statement = 
   let param = Procedure.to_var param_statement in
   let (_, attrs) = param in 
   if Var.is_struct param then
     begin
       (* Var.pprint param; pw ""; *)
       let struct_name = Var.get_struct_name param in
       (* pw struct_name; *)
       let fields = snd (List.find (fun (x, _) -> x = struct_name) structures) in
       let fields = (fun (n, e) -> (Bytes.concat "." n, e)) |>>| fields in
       (* pi (List.length fields); pn ""; *)
       Block.PARALLEL (
         Block.ASSIGN(param, Term.NULL, Block.SKIP, loc),
         Block.CONS(Exp.VAR param, fields, Block.SKIP, loc),
         body, loc), i
     end
   else
     begin 
       let i = Formula.fresh_variable i in
       let vi = Var.toVar (Formula.i_to_v i) in
       let (vi : Var.t) = Var.set_attributes vi attrs in
       Block.PARALLEL(
         Block.ASSIGN(param, Term.NULL, Block.SKIP, loc),
         Block.MAPS(param, vi, Block.SKIP, loc),
         body, loc), i
     end

let get_deterministic_parameter loc structures (body, i) param_statement = 
   let param = Procedure.to_var param_statement in
   let (_, attrs) = param in 
   if Var.is_struct param then
     begin
       (* Var.pprint param; pw ""; *)
       let struct_name = Var.get_struct_name param in
       (* pw struct_name; *)
       let fields = snd (List.find (fun (x, _) -> x = struct_name) structures) in
       let fields = (fun (n, e) -> (Bytes.concat "." n, e)) |>>| fields in
       (* pi (List.length fields); pn ""; *)
       Block.CONS(Exp.VAR param, fields, body, loc), i
     end
   else
     begin 
       let i = Formula.fresh_variable i in
       let vi = Var.toVar (Formula.i_to_v i) in
       let (vi : Var.t) = Var.set_attributes vi attrs in
       Block.MAPS(param, vi, body, loc), i
     end


let verify_procedure is_det (procs, vars, (structures: Structure.t list)) ((pre : Formula.t), (procname, (params : Block.t list), body), post) loc global :  (int * (Formula.t * Formula.t)) list =
  let th = (Big_int.big_int_of_int 1000000) in
  let body', max, branches = 
    if pre = Formula.empty then
      begin
        (** Classify parameters *)
        let (structure_params, rest) = List.partition (fun x -> let x = Procedure.to_var x in Var.is_struct x && (not (Var.is_ptr x))) params in
        let (pointer_params, rest)   = List.partition (fun x -> let x = Procedure.to_var x in Var.is_ptr x) rest in (** All kinds of parameters *)
        let (array_params, ordinary_params) = List.partition (fun x ->
            match x with
              Block.ARRAY (_, _, _, _, _) -> true
            | _ -> false
          ) rest in
        (** deterministic by opportunity *)
(*        let refs, unrefs = classify_params [] pointer_params body in
        let (body', i) = (get_deterministic_parameter loc structures) |->> ((body, 0), refs) in
          let body' = (get_null_parameter loc structures) |->> (body', unrefs) in *)
        (**)
        let (body', i) =
          if is_det then
            (get_deterministic_parameter loc structures) |->> ((body, 0), pointer_params) 
          else
            (get_nondeterministic_parameter loc structures) |->> ((body, 0), pointer_params)
        in  (**)
        VcpAnalyze.reset procs;
        let (max, branches) = VcpAnalyze.get_branches body' in
        (**)
        let (body', i) = 
          if (not is_det) && (Big_int.gt_big_int branches th) then
            (get_deterministic_parameter loc structures) |->> ((body, 0), pointer_params)
          else
            (body', i)
        in (**)
        let body' = Block.join body' structure_params in 
        Block.join body' array_params, max, branches
          end
      else
        begin
          VcpAnalyze.reset procs;
          let (max, branches) = VcpAnalyze.get_branches body in
          body, max, branches
        end
  in
(*  VcpAnalyze.reset procs;
    let (max, branches) = VcpAnalyze.get_branches body' in *)
  linear.contents <- false; (* (Big_int.gt_big_int branches th); *)
 
    let vparams = Procedure.to_var |>>| params in
    let pre = Formula.be_typed pre vparams loc in
    let post = Formula.be_typed post vparams loc in
    let p_fvs = Block.fv body' in
    let global' = (fun g -> filter_global g p_fvs) |>>| global in
    count.contents <- 0;
    (* Block.pprint 0 body'; *)
    validate (Formula.merge global' pre, body', post) 0 (procs, vparams @ vars, structures) 

  let rec validate_global make_post (procs, vars, (structures : Structure.t list)) fv global = function
    | [] -> []
    | Global.STATEMENT (Block.ASSIGN (v, e, _, loc))::xs ->
      let vars = update_vars vars v e loc in
      let (global, fv') = Formula.assign ~bypass:true vars global v [e] fv loc in
      validate_global make_post (procs, vars, structures) fv' global xs
    | Global.PROC ((proc_name, _, _) as proc, pre1, post, _, loc)::xs ->
      (* pw (Var.toStr proc_name); pn "()"; *) 
      let y = verify_procedure make_post (procs, vars, structures) (pre1, proc, ([],[])) loc (fst global) in
      (* pi (List.length y); *)
      let (pres : (Formula.t * Formula.t) list) = (fun (_, (pre1, post1)) ->
          (** Filter out special control variables *)
          let filt =  (fun (a,b,c,d) -> 
             let b' = (fun x ->
              match x with
              | BExp.UNIT (x, _, _) -> let sx = Term.toStr x in if sx = "$return" || sx = "$continue" || sx = "$break" then false else true
              | _ -> false
                ) |>- b in
             let fv = (List.concat (BExp.fv |>>| b')) @ (Term.toStr |>>| (List.concat (Pointer.fvs |>>| c))) @ (fst |>>| (List.concat (Predicate.fvs |>>| d))) in
             let a' = List.sort_uniq (Bytes.compare) ((fun v -> v |<- fv) |>- a) in
             
             (a',b',c,d)
            ) in
          (filt |>>| (fst pre1), snd pre1),
          (filt |>>| (fst post1), snd post1)
        ) |>>| y
      in
      (*      pw ">>"; Formula.pprint pre''; pn "";*)
      let procs' = (fun (proc', pre', post') ->
          if Procedure.get_name proc' = proc_name && post' = Formula.empty then
            begin
              try
                (proc', pre', fst (List.hd pres))
              with
                _ -> (proc', pre', Formula.empty) (* raise (StError("velidate global - pres")) *)
            end
          else
            (proc', pre', post')
        ) |>>| procs in
      (* pw (Var.toStr proc_name); pn " & "; *)
      if make_post then
        begin
          iterS (fun (x, y) -> Formula.pprint x; p " |- \n"; Formula.pprint y (* iterS Formula.pprint "| " pres *)) "\n\n" pres;
          pn "\n";
        end
      else
        begin
          print_warning (Var.toStr proc_name);
          erase_warning ();
        end;
      (* iterS (fun (_, entl) -> Entailment.pprint entl) "\n\n" y;
      pn "";
         pn ""; *)
      let ys = validate_global make_post (procs', vars, structures) fv global xs in 
      y @ ys      
    | _::xs -> validate_global make_post (procs, vars, structures) fv global xs

let validate_system (x : Global.t list) =
   let structures = !Block.structures in
   (* List.fold_left (fun a y ->
       match y with
         Global.STRUCT (structure, _) ->
         structure::a
       | _ -> a) [] x in *)
   (* p "Total structures: "; pi (List.length structures); pn ""; *)
   (* iterS Structure.pprint "\n" structures; *)
   let procs = List.fold_left (fun a y ->
       match y with
         Global.PROC (proc, pre, post, _, _) -> (proc, pre, post)::a
       | _ -> a ) [] x in
   let entls = validate_global true (procs, [("$return", []);("$ret", []);("$break", []);("$continue", [])], structures) 0 Formula.empty x in
   (* pw "Total Entailments:";
   pi (List.length entls); *)
   entls
  
*)