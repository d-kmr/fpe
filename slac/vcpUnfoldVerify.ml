open Ftools
open VcpTranslate
open VcpBase

type t = {
  filename : string;
  fullpath : string;
  gs : Global.t array;
  structs : Structure.t list;
  mutable is_executed : bool;
  mutable global : Formula.t }

let linear = ref false
let count = ref 0
(*
let l_locs = ref []

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

let entl_check_c form = 
(*  ConvFtoK.checksat_one_faisal form *)
  let zero = Term.EXP (Exp.CONST 0) in
  let false_bexp = BExp.UNIT (zero, Op.NE, zero) in
  let entl = ([form], [([],[false_bexp],[],[])]) in
    not (ConvFtoK.decide_ps_faisal [entl]) 
  

let check_c verbose form =
  if !Options.old_sat then
    List.filter (fun f -> not (ucheck_c verbose f)) form 
  else
    List.filter (fun f -> entl_check_c f) form
*)

let find_proc name (gs : Global.t array) =
  let rec find i =
    if i = Array.length gs then
      i, None
    else
      let m = Array.get gs i in
      match m with
        Global.PROC (((proc_name, a0), a1, a2), a3, a4, a5, a6) ->
        if proc_name = name then
          i, Some (Global.PROC (((proc_name, a0), a1, a2), a3, a4, a5, a6))
        else
          find (i+1)
      | _ -> find (i+1)
  in
  find 0
(*
let find_proc_in_modules name (modules : t array)  =
  let rec find i =
    if i = Array.length modules then
      None
    else
      let mo = Array.get modules i in
      match find_proc name mo.gs with
        _, None -> find (i+1)
      | _, Some x -> Some mo
  in
  find 0
*)

let find_module name (a_modules : t array) =
  let rec find i =
    if i = Array.length a_modules then
      Array.get a_modules 0
    else
      let m = Array.get a_modules i in
      if m.filename = name then
        m
      else
        find (i+1)
  in
  find 0


let to_t (a1, a2, a3, a4, a5, a6) = {filename = a1; fullpath = a2; gs = Array.of_list a3; structs = a4; is_executed = a5; global = a6}
(*
let balance_entailment (lhs, rhs)=
  if rhs = [] then
    (lhs, rhs), [], []
  else
    let (exs_r, pure_r, pointer_r, pred_r) = List.hd rhs in
    let (exs_l, pure_l, pointer_l, pred_l) = List.hd lhs in
    let pointers = (fun x -> Term.toStr (fst x)) |>>| pointer_r in
    let array_heads = (fun (_, ls) -> Term.toStr (List.hd ls)) |>>| pred_r in
    let rest_pointer = (fun (ptr, _) -> not ((Term.toStr ptr) |<- pointers)) |>- pointer_l in
    let rest_array = (fun (_, ls) -> not (Term.toStr (List.hd ls) |<- array_heads)) |>- pred_l in
    (lhs, [(exs_r, pure_r, pointer_r @ rest_pointer, pred_r @ rest_array)] @ (List.tl rhs)), rest_pointer, rest_array
    *)

let update_vars vars var exp loc =
  let v = fst var in
  if not (List.exists (fun (w, _) -> w = v) vars) && (exp = Term.NULL || exp = Term.EXP Exp.NOTHING) then
    var::vars
  else if (Bytes.get v 0) = '.' then
    let attrs = Term.infer_attributes vars loc exp in
    (v, attrs)::vars
  else
    vars


let execute_global mo vars fv : t * int =
  if mo.is_executed then
    begin
      if !Options.to_be_report_printed then
        begin
          prerr_string mo.filename; prerr_string ": "; prerr_endline "Used module"
        end;
      mo, fv
    end
  else
    begin
      if !Options.to_be_report_printed then
        begin
          prerr_string mo.filename; prerr_string ": "; prerr_endline "First time module"
        end;
      let len = Array.length mo.gs in
      let rec execute i pre vars fv =
        if i = len then
          pre, fv
        else
          match Array.get mo.gs i with
            Global.STATEMENT (Block.ASSIGN (v, e, _, loc)) ->
            let vars = update_vars vars v e loc in
            let (pre', fv') = Formula.assign ~bypass:true vars pre v [e] fv loc in
            execute (i+1) pre' vars fv'
          | _ ->
            execute (i+1) pre vars fv
      in
      let glo, fv = execute 0 Formula.empty vars fv in
      mo.is_executed <- true;
      mo.global <- glo;
      mo, fv
    end

(*

let rec classify_params (refs : Block.t list) unrefs = function
    Block.SKIP -> refs, unrefs
  | Block.ASSIGN (_, _, pr, _) -> classify_params refs unrefs pr
  | Block.CONS (e_v, _, pr, _) ->
    let refs, unrefs = classify_params refs unrefs pr in
    let matched, unmatched = List.partition (fun x -> Exp.VAR (Procedure.to_var x) = e_v) refs in
    unmatched, matched @ unrefs
  | Block.LOOKUP (_, pt, _, pr, _) ->
    let matched, unmatched = List.partition (fun x -> (Procedure.to_var x) = Term.decode pt) unrefs in
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
  
let get_null_parameter loc structures body param_statement =
  let param = Procedure.to_var param_statement in
  Block.ASSIGN(param, Term.NULL, body, loc) 

let get_fields param structures i =
  let texs = ref [] in
  let struct_name = Var.get_struct_name param in
  let fields =
    try
      snd (List.find (fun (x, _) -> x = struct_name) structures)
    with
    | _ -> []
  in
  let i = Formula.fresh_variable i in
       let fields = List.mapi (fun j (n, e) ->
           let v = Formula.i_to_v (j+i) in
           texs.contents <- !texs @ [v];
           (Bytes.concat "." n, Term.EXP (Exp.VAR (v, [Var.EXQ])) )
    ) fields in
  fields, i, !texs
    

let get_deterministic_parameter loc structures (body, i, exs) param_statement = 
   let param = Procedure.to_var param_statement in
   let (_, attrs) = param in
   if Var.is_struct param then
     begin
       let fields, i, texs = get_fields param structures i in
(*       (* Var.pprint param; pw ""; *)
       let struct_name = Var.get_struct_name param in
       (* pw struct_name; *)
       let fields = snd (List.find (fun (x, _) -> x = struct_name) structures) in
       let i = Formula.fresh_variable i in
       let fields = List.mapi (fun j (n, e) ->
           let v = Formula.i_to_v (j+i) in
           texs.contents <- !texs @ [v];
           (Bytes.concat "." n, Term.EXP (Exp.VAR (v, [Var.EXQ])) )
         ) fields in
         (* pi (List.length fields); pn ""; *) *)
       Block.CONS(Exp.VAR param, fields, body, loc), (i + List.length fields), exs @ texs
     end
   else
     begin 
       let i = Formula.fresh_variable i in
       let sv = Formula.i_to_v i in
       let vi = Var.toVar sv in
       let (vi : Var.t) = Var.set_attributes vi attrs in
       Block.MAPS(param, vi, body, loc), i, exs
     end

let check_mem_leak formulas l =
  (* pn (Locs.toStr l);
  Formula.pprint formulas;
     pn "\n"; *)
  let ret = Term.encode ("$ret", []) in
  (*
  let formulas' = (fun (a,b,c,d) ->
      let c' = (fun (p, _) ->
          let v = Term.decode p in
          (Var.is_ptr v) && (not (Formula.(===) b p ret)) && (not (Var.is_param v)) && (not (Var.is_global v))
        ) |>- c in
      (a,b,c',d)
    ) |>>| formulas in
  *)
  if List.exists (fun (a,b,c,d) ->
      
      List.exists (fun (p,_) ->
          let v = Term.decode p in
          
          (Var.is_ptr v) && (not (Formula.(===) b p ret)) && (not (Var.is_param v))
        ) c
    ) formulas then
    pn ("Memory Leak at " ^ (Locs.toStr l))
;;

let rec validate ((pre, program, post) : Formula.t * Block.t * Formula.t) (fv:int) ((modules_a, vars, structures, procs) as packs) : (int * (Formula.t * Formula.t)) list =
  (* let pre11 = pre in *)
  (*  let n1 = List.length pre in *)
  let pre = uniq pre in
  (*  let n2 = List.length pre in *)
  (* prerr_int n1;
  prerr_string " -> ";
  prerr_int n2;
  prerr_endline "";
     Formula.pprint pre; pn "\n"; *)
  let pre = check_c false pre in
  if pre = [] then
    begin
  (*    pn "[]=";
        Formula.pprint pre11; pn "\n"; *)
      []
    end
  else
    begin
    match program with
    | Block.SKIP ->
      [(fv, (pre, post))]              
    | Block.ASSERT (formula, pr, _) ->
      (fv, (pre, formula)) :: validate (formula, pr, post) fv packs        
    | Block.ASSIGN (var, exp, program, l) ->
       let (vars : Var.t list) = update_vars vars var exp l in  (** vars := vars ++ var *)      
      begin
        (** SIMP(Ex x'(x=exp[x:=x'] & (PI & SIGMA)[x:=x'])) *)
        let exps = (fun _ -> exp) |>>| pre in                       (** if pre is [PI1; PI2] then exps = [exp; exp] *)
        let (pre', fv') = Formula.assign vars pre var exps fv l in  (** fv' := fv' ++ x', pre' = pre[x:=e] *)

        (** Memory Leak test *)
        if Var.toStr var = "$ret" then
          begin
            if !Options.in_place_check then
              check_mem_leak pre' l;
            List.iter (fun (_, eqs, ptr_list, _) ->
                let allocated_memory = (fun (pt, _) -> let vpt = Term.decode pt in Var.is_struct vpt && Var.is_ptr vpt && (not (Var.is_param vpt)) ) |>- ptr_list in
                let non_return_memory = List.filter (fun (pt, _) -> not (Formula.(===) eqs exp pt) ) allocated_memory in
                if List.length non_return_memory > 0 then
                  begin
                    List.iter (fun ptr ->
                        match Formula.get_real_var eqs (fst ptr) with
                          Some (sptr) -> warn ("Memory Leak (left over) by " ^ sptr) l () (* "ML & " *)
                        | None -> ()
                      ) non_return_memory
                  end
              ) pre'
          end;
        validate (pre', program, post) fv' (modules_a, vars, structures, procs)
      end
    | Block.CONS (e_v, ts, pr, l) ->                                            (** v is expected to be properly typed if not already in vars *)
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
          let (_, eqs, ptrs, _) = List.hd pre in
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
          let t_v       = Term.encode v in
          let nulls     = (fun _ -> Term.NULL) |>>| pre in
          let (pre1,fv) =
            if Var.is_ptr v && (not (Var.is_param v)) then
              begin
                Formula.assign vars pre v nulls fv l
              end
            else
              [], fv
          in
          let pre'      = Formula.substitute t_v t_fv pre l in 
          let pre''     = Formula.add_to_spatial pre' (t_v, ts) in                  (** CAUTION: dummy field is used *)
          let pre'''    = Formula.is_memory_leak eqs ptrs t_v pre'' pre l in
          
          validate (pre''' @@ pre1, pr, post) fv' (modules_a, vars, structures, procs)
        end
      else
        validate (pre, pr, post) fv (modules_a, vars, structures, procs)
    | Block.LOOKUP (v, ((Term.EXP (Exp.VAR ptv)) as pt), "*", pr, l) ->
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
        ) |>>| pre
      in
      let (pres, progs) = List.split pres_progs in
      validate (pres, List.hd progs, post) fv packs
    | Block.LOOKUP (v, pt, "*", pr, l) ->
      if Var.is_array (Term.decode pt) then 
        let pres =
          (fun (a,b,c,d) ->
             let mt = (fun (ptr, ds) -> Term.toStr ptr = Term.toStr pt) |>- c in
             let new_pre, value, fv = 
               match mt with
                 [(_, (_,value)::[])] -> [], value, fv
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
                        let pre' =  (i_s::a, pure @ b, (new_loc, ["*", tx'])::c, pred1::pred2::(rest @ unmatched)) in
                        pre'
                     )
                     |>>| matched
                   in
                   new_pre, tx', fv
                 end                 
             in
             new_pre, value, fv
          ) |>>| pre in
        let new_pre = List.concat ((fun (a,_,_) -> a) |>>| pres) in
        let value = List.hd ((fun (_,a,_) -> a) |>>| pres) in
        let entl = 
          if new_pre = [] then
            let v_t = (fun _ -> value) |>>| pre in
            let (pre', fv') = Formula.assign vars pre v v_t fv l in
            validate (pre', pr, post) fv packs 
          else
            let v_t = (fun _ -> value) |>>| new_pre in
            let (new_pre', fv') = Formula.assign vars new_pre v v_t fv l in            
            (fv, (pre, new_pre)) :: validate (new_pre', pr, post) fv packs
        in
        entl 
      else
        validate (pre, pr, post) fv packs
    | Block.LOOKUP (v, pt, i, pr, l) ->                                        (** {A * pt->(i:v_t)} v = pt->i {B} |- {A * pt->(i:v_t)} v = v_t {B} *)
      if Var.is_ptr (Term.decode pt) then
        let fields, fv', exs = get_fields (Term.decode pt) structures fv in
        (*
        let post1' =
          (fun (ex, pures, ptrs, preds) ->
             let pures' = (fun bexp ->
                 match bexp with
                   BExp.UNIT (lhs, Op.EQ, rhs) -> not ((Formula.(===) pures lhs pt) && (rhs = Term.NULL)) 
                 | _ -> true
               ) |>- pures
             in
             if List.exists (fun (pt', _) -> Formula.(===) pures pt pt') ptrs then
               (ex, pures', ptrs, preds)
             else
               (ex @ exs, pures', ptrs @ [(pt, fields)], preds)
               (*          (ex @ exs, pures, [(pt, fields)], []) *)
          ) |>>| pre in *)
        let pre' = (fun (ex, pures, ptrs, preds) ->
            let ptrs' = (fun (ptr,_) -> Formula.(===) pures ptr pt) |>- ptrs in
            (ex, pures, ptrs', [])
          ) |>>| pre in
        let post2' = [((Term.toStr) |>>| (snd |>>| fields), [], [(pt, fields)], [])] in
        let entl = Formula.purify (pre', post2') in
        let v_t : Term.t list  = Formula.get_from pre pt i l in
        let (pre', fv') = Formula.assign vars pre v v_t fv l in
        if !Options.in_place_check then
          begin
            if !Options.in_place_entl then
              begin
                pn "\n--------------";
                pn (Locs.toStr l);
                Formula.pprint_entl entl;
              end;
            if not (ConvFtoK.decide_ps_faisal [entl]) then
              pn ("Null Pointer Derefernce at "  ^ (Locs.toStr l));
            validate (pre', pr, post) fv packs
          end
        else
          (fv, entl)::(validate (pre', pr, post) fv' packs)
      else
        let v_t : Term.t list  = Formula.get_from pre pt i l in
        let (pre', fv') = Formula.assign vars pre v v_t fv l in
        validate (pre', pr, post) fv' packs
    | Block.MUTATION ((Term.EXP (Exp.VAR ptv)) as pt, "*", t, pr, l) ->        (** {A & pt=>z} z = t {B} |- {A & pt=>z} *pt = t {B} *)
      let (_, eqs, _, _) = List.hd pre in
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
      if Var.is_array (Term.decode pt) then
        begin 
          let pres : ((Formula.t * Formula.t) list) =
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
                    )
                    |>>| matched
                  in
                  let pre' = fst |>>| entls_pre' in
                  let new_pre = snd |>>| entls_pre' in
                  pre', new_pre
                end
            ) |>>| pre in
          let pre' = List.concat (fst |>>| pres) in
          let new_pre = List.concat (snd |>>| pres) in
          let (entls : (int * (Formula.t * Formula.t)) list) = validate (new_pre, pr, post) fv packs in
          if pre' = [] then
            entls
          else
            (fv, (pre, pre'))::entls
        end
      else
        begin
          (* let pt = Term.be_typed vars l pt in *)
          let ts = (fun _ -> t) |>>| pre in
          
          if Var.is_ptr (Term.decode pt) then
            begin
            let fields, fv', exs = get_fields (Term.decode pt) structures fv in
            (* let post1' =
              (fun (ex, pures, ptrs, preds) ->
                 let pures' = (fun bexp ->
                       match bexp with
                         BExp.UNIT (lhs, Op.EQ, rhs) -> not (((Term.toStr lhs) = (Term.toStr pt)) && (rhs = Term.NULL)) 
                       | _ -> true
                     ) |>- pures
                 in
                 if List.exists (fun (pt', _) -> Formula.(===) pures pt pt') ptrs then
                   (ex, pures', ptrs, preds)
                 else
                   (ex @ exs, pures', ptrs @ [(pt, fields)], preds)
                   (*          (ex @ exs, pures, [(pt, fields)], []) *)
              ) |>>| pre in *)
            let pre' = (fun (ex, pures, ptrs, preds) ->
                let ptrs' = (fun (ptr,_) -> Formula.(===) pures ptr pt) |>- ptrs in
                (ex, pures, ptrs', [])
              ) |>>| pre in
            let post2' = [((Term.toStr) |>>| (snd |>>| fields), [], [(pt, fields)], [])] in
            let entl = Formula.purify (pre', post2') in
            entl(*
            let entl = Formula.purify (pre, post1') in *)
            let pre' = Formula.set_to pre pt i ts l in

            
          
(*            p (Locs.toStr l);
            pn " #";
            Formula.pprint pre; pn "";
            Formula.pprint post1'; pn "";
              Formula.pprint pre'; pn ""; *)
            if !Options.in_place_check then
              begin
                if !Options.in_place_entl then
                  begin
                    pn "\n--------------";
                    pn (Locs.toStr l);
                    Formula.pprint_entl entl;
                  end;
                if not (ConvFtoK.decide_ps_faisal [entl]) then
                  pn ("Null Pointer Derefernce at "  ^ (Locs.toStr l));
                validate (pre', pr, post) fv packs
              end
            else
              (fv, entl)::(validate (pre', pr, post) fv packs)
            end
          else
            let pre' = Formula.set_to pre pt i ts l in
            validate (pre', pr, post) fv packs
        end
    | Block.DISPOSE (pt, pr, l) -> 
      let (_, eqs, _, _) = List.hd pre in
      Formula.new_ptr.contents <- (List.filter (fun x -> not (Formula.(===) eqs x pt)) !Formula.new_ptr);
      if Var.is_ptr (Term.decode pt) then
        let fields, fv', exs = get_fields (Term.decode pt) structures fv in
        (* let post1' =
          (fun (ex, pures, ptrs, preds) ->
             let pures' = (fun bexp ->
                 match bexp with
                   BExp.UNIT (lhs, Op.EQ, rhs) -> not ((Formula.(===) pures lhs pt) && (rhs = Term.NULL)) 
                 | _ -> true
               ) |>- pures
             in
             if List.exists (fun (pt', _) -> Formula.(===) pures pt pt') ptrs then
               (ex, pures', ptrs, preds)
             else
               (ex @ exs, pures', ptrs @ [(pt, fields)], preds)
               (*          (ex @ exs, pures, [(pt, fields)], []) *)
          ) |>>| pre in *)
        let pre' = (fun (ex, pures, ptrs, preds) ->
            let ptrs' = (fun (ptr,_) -> Formula.(===) pures ptr pt) |>- ptrs in
            (ex, pures, ptrs', [])
          ) |>>| pre in
        let post2' = [((Term.toStr) |>>| (snd |>>| fields), [], [(pt, fields)], [])] in
        let entl = Formula.purify (pre', post2') in
        (*
          let entl = Formula.purify (pre, post1') in *)
        let pre' = Formula.delete_from pre pt l in
        if !Options.in_place_check then
          begin
            if !Options.in_place_entl then
              begin
                pn "\n--------------";
                pn (Locs.toStr l);
                Formula.pprint_entl entl;
              end;
            if not (ConvFtoK.decide_ps_faisal  [entl]) then
              pn ("Null Pointer Derefernce at "  ^ (Locs.toStr l));
            validate (pre', pr, post) fv packs
          end
        else
          (fv, entl) :: (validate (pre', pr, post) fv packs)
      else
        let pre' = Formula.delete_from pre pt l in
        validate (pre', pr, post) fv packs
    | Block.IF (e, p1, p2, pr, l) ->
      let pre1 = Formula.add_to_formula pre e in
      let pre2 = Formula.add_to_formula pre (BExp.complement e) in 

      let p1' = Block.compose pr p1 in
      let p2' = Block.compose pr p2 in
(*      let b1  = (check_c false pre1) = [] in
      let b2  = (check_c false pre2) = [] in
      if !linear then
        if b1 && b2 then
          raise (StError ("IF problem"))
        else if b1 then
          begin
            validate (pre2, p2', post) fv packs
          end
        else
          begin
            validate (pre1, p1', post) fv packs
          end
      else *)
      let entl1 : (int * (Formula.t * Formula.t)) list = validate (pre1, p1', post) fv packs in
      let entl2 = validate (pre2, p2', post) fv packs in
      let entl1', entl1'' = List.partition (fun (_, (_, post)) -> post != []) entl1 in
      let entl2', entl2'' = List.partition (fun (_, (_, post)) -> post != []) entl2 in
      let post1' = List.concat ((fun (_, (pre, _)) -> pre) |>>| entl1'') in
      let post2' = List.concat ((fun (_, (pre, _)) -> pre) |>>| entl2'') in
      (* prerr_string "IF: "; prerr_endline (Locs.toStr l); *)
      (* let entl12 = validate (post1' @ post2', pr, post) fv packs in *) 
      let entl12 = (0, (post1' @ post2', [])) in 
      entl1' @ entl2' @ [entl12]
    | Block.MAPS (_from, _to, body, l) ->
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
        ) |>>| pre in
      validate (form, body, post) fv packs
    | Block.PARALLEL (pr1, pr2, pr, l) ->
      List.append (validate (pre, Block.compose pr pr1, post) fv packs)  (validate (pre, Block.compose pr pr2, post) fv packs)
    | Block.PROCCALL (proc_name, args, body, l) ->
      let update_locs () =
        if not (l |<- !l_locs) then
          l_locs.contents <- !l_locs @ [l]
      in
      if !Options.to_be_report_printed then
        begin
          prerr_string proc_name; prerr_string " (Stack: "; List.iter (fun pr -> prerr_string pr; prerr_string ",") procs; prerr_endline ")";
          prerr_endline (Locs.toStr l)
        end;
      if proc_name |<- procs then
        begin
          if not (l |<- !l_locs) then
            begin
              if !Options.to_be_report_printed then
                begin
                  prerr_string "Recursion found: "; prerr_endline proc_name
                end
            end;
          validate (pre, body, post) fv packs
        end
      else
      begin
        (** Search proc in modules_a *)
        match find_proc_in_modules proc_name modules_a with
          None ->
          if not (l |<- !l_locs) then
            begin
              if !Options.to_be_report_printed then
                begin
                  prerr_string "Not Found: "; prerr_endline proc_name;
                end;
              update_locs ()
            end;
          validate (pre, body, post) fv packs
        | Some mo ->
          begin
            match find_proc proc_name mo.gs with
              _, None ->
              update_locs ();
              validate (pre, body, post) fv packs
            | i, Some (Global.PROC ((p_name, p_params, p_body), p_pre, p_post, p_extra, p_loc)) ->
              let fv, p_pre', p_post', p_extra' = 
                if p_post = [] then
                  begin
                    (** Not unfolded yet. So, unfold it. *)
                    (** Make precondition of the procedure *)
                    let mo, fv = execute_global mo vars 0 in
                    let fv, p_pre = make_precondition p_params p_body mo.global fv mo.structs p_loc packs in
                    if !Options.to_be_report_printed then
                      begin
                        prerr_string "Unfolding: "; prerr_string mo.fullpath; prerr_string " :: "; prerr_endline proc_name
                      end;
                    let entls1 = validate (p_pre, p_body, []) fv (modules_a, vars, structures, procs @ [proc_name]) in 
                    let extract_post xs =
                      let xs' = (fun (pre1, post1) -> post1 = []) |>- xs in
                      List.concat ((fun (pre1, _) -> pre1) |>>| xs')
                    in
                    let entls1 = Formula.purify |>>| (snd |>>| entls1) in
                    let p_post = extract_post entls1 in
                    
                    let extract_extra xs =
                      let xs' = (fun (pre1, post1) -> post1 != []) |>- xs in
                      xs'
                    in
                    let p_extra = extract_extra entls1 in
                    let proc' = Global.PROC ((p_name, p_params, p_body), p_pre, p_post, p_extra, p_loc) in
                    Array.set mo.gs i proc';
                    fv, p_pre, p_post, entls1
                  end
              else
                begin
                  if !Options.to_be_report_printed then
                    begin
                      prerr_string "Found Unfolded "; prerr_endline proc_name
                    end;
                  fv, p_pre, p_post, p_extra
                end
              in
              (** Substitute all of pre, post, and extra *)
              let args = 
                if (List.length p_params) < (List.length args) then
                  let rec take n = function
                      [] -> []
                    | x::xs -> if n = 1 then [x] else (x::(take (n-1) xs))
                  in
                  take (List.length p_params) args
                else
                  args
              in
              if (List.length p_params) = (List.length args) then
                begin
                  
                  let params_in_term = (fun p -> Term.encode (Procedure.to_var p)) |>>| p_params in
                  let par_args = List.map2 (fun p a -> (p, a)) params_in_term args in
                  let (s_a, s_b, s_c, s_d) = List.hd ((fun f (pp, a) -> Formula.substitute pp a f l) |->> (p_pre', par_args)) in
                  
                  let s_c_p = Term.toStr |>>| (fst |>>| s_c) in 
                  let extra = (fun (a', b', c', d') -> (a', b', (fun (p,_) -> not ((Term.toStr p) |<- s_c_p)) |>- c', d')) |>>| pre in
                  let p_pre_pairs = List.map2 (fun (a1,b1,c1,d1) (_,_,c2,_) ->
                      let temp = (fun (p, f) ->
                          try
                            let (p', f') =
                              try
                                List.find (fun (p',_) -> Term.toStr p' = Term.toStr p) c2
                              with
                              | _ -> (p, f) (* prerr_string "ERROR: List.find"; raise SError *)
                            in
                            let tf = List.map2 (fun (_, a) (_, b) -> (a, b)) f f' in
                            (p', f'), tf
                          with
                          | _ -> (p, f), []
                        ) |>>| s_c
                      in
                      let s_c', pairs = List.split temp in
                      let pairs = List.concat pairs in
                      (s_a @@ a1, s_b @@ b1, s_c' @ c1, s_d @ d1), pairs
                    ) extra pre
                  in
                  let pre' = (fun (a1,b1,c1,d1) ->
                      let c1' = (fun (ptr, _) -> List.exists (fun arg -> Formula.(===) b1 arg ptr) args ) |>- c1 in
                      (a1,b1,c1',d1)
                    ) |>>| pre in
                  let _, l_pairs = List.split p_pre_pairs in
                  let entl = (pre', [(s_a, s_b, s_c, s_d)]) in
                  (*
                  let p_pre', l_pairs = List.split p_pre_pairs in
                  let entl = (pre, p_pre') in *)
                  (* let p_pre' = List.fold_left (fun f (pp, a) -> Formula.substitute pp a f l) p_pre' par_args in
                     Formula.pprint p_pre'; *)
                  (* let (pre1, pre2), restptr, restpred  = balance_entailment (pre, p_pre') in *)
                  (* let entl = (Formula.to_emp_fields pre1, pre2) in *)
                  let p_post' = (fun f (p, a) -> Formula.substitute p a f l) |->> (p_post', par_args) in
                  let p_post' = List.concat (
                      List.map2 (fun (a1, b1, c1, d1) pairs ->
                          let post' = (fun f (p, a) -> Formula.substitute p a f l) |->> (p_post', pairs) in
                          (fun (pa, pb, pc, pd) -> (pa @@ a1, pb @@ b1, pc @@ c1, pd @@ d1)) |>>| post' 
                        ) extra l_pairs)
                  in                  
                (* let p_post' = (fun (a,b,c,d) -> (a,b,c @ restptr, d @ restpred)) |>>| p_post' in *) 
                  (** NEED CORRECT SUBSTITUTION ABOUT something inside pointers. *)
                  let p_extra' = (fun p_ex ->
                      (fun (fa, fb) (p, a) ->
                         (Formula.substitute p a fa l, Formula.substitute p a fb l)
                      ) |->> (p_ex, par_args)
                    ) |>>| p_extra'
                  in
                  update_locs ();
(*                Formula.pprint pre; p "|-"; Formula.pprint p_pre'; pn "";
                iterS (fun (_, (a,b)) -> Formula.pprint a; p "|-"; Formula.pprint b) "\n" p_extra';
                pn "...";
                  Formula.pprint post; *)
                
                  let p_extra' = (fun x -> (0, x)) |>>| p_extra' in
                  if !Options.in_place_check then
                    begin
                      if not (ConvFtoK.decide_ps_faisal [entl]) then
                        pn  ("Null Argument at " ^ (Locs.toStr l));
                      validate (p_post', body, post) fv packs
                    end
                  else
                    (0, entl) :: p_extra' @ (validate (p_post', body, post) fv packs)
                end
              else
                begin
                  prerr_string "Parameter - argument mismatch: "; prerr_string proc_name;
                  prerr_string " (Stack: "; List.iter (fun pr -> prerr_string pr; prerr_string " ") procs; prerr_endline ")";
                  prerr_string "From: "; prerr_endline mo.fullpath;
                  prerr_string "Params: ("; prerr_int (List.length p_params); prerr_string "): "; List.iter (fun p -> prerr_string (Var.toStr (Procedure.to_var p)); prerr_string " ") p_params; prerr_endline "";
                  prerr_string "Args: (";  prerr_int (List.length args); prerr_string "): "; List.iter (fun a -> prerr_string (Term.toStr a); prerr_string " ") args; prerr_endline "";
                  update_locs ();
                  validate (pre, body, post) fv packs
                end
                
            | _ -> [] (** This case will never comes. Just to avoid warning *)

          end
      end
(*
| Block.PROCCALL (str, args, body, l) ->
      begin
        let (_, eqs, ptrs, _) = List.hd pre in 
        List.iter (fun x ->
            let x = Term.be_typed vars l x in
            if Formula.(===) eqs x Term.NULL then
              match Formula.get_real_var eqs x with
              | None ->
                ()
              | Some s ->
                warn (s ^ " is a Null Argument") l ()
          ) args; 
        match body with
          Block.ASSIGN (v1, e1, b1, l1) when Term.toStr e1 = "$ret" -> 
          let (is_ptr, is_struct, type_name) = 
            try
              let ((name, param_statements, _), pre1, post1) = 
                List.find (fun ((name, _, _), _, _) -> Var.toStr name = str) [] in
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
      end *)
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
      
      if inv = [([],[],[],[])] then
        begin
          (* prerr_string "WHILE: "; prerr_endline (Locs.toStr l); *)
          validate (pre, Block.IF (b, block, Block.SKIP, body, l), post) fv packs
        end
      else
        let f, f' = List.split ((fun (x,y,z,w) -> (x, b::y, z, w), (x, (BExp.complement b)::y, z, w)) |>>| inv) in
        let ent1 = (pre, f) in
        let entl1 = validate (f, block, inv) fv packs in
        let entl2 = validate (f', body, post) fv packs in
        (fv, ent1)::(entl1 @ entl2)
    | Block.ARRAY (a, b, tl, body, _) ->
      let pre' = 
        if tl = [] then
          let array_pred = ("Array", [Term.encode a; b]) in
          (fun (exqs, eqs, c, pred) -> (exqs, eqs, c, array_pred::pred)) |>>| pre
        else
          (fun (exqs, eqs, c, pred) -> 
             let pointers = List.mapi (fun i x -> (Term.EXP (Exp.BINOP (Exp.VAR a, Op.ADD, Exp.CONST i)), [("*", x)]) ) tl in
             (exqs, eqs, pointers @ c, pred)
          ) |>>| pre
      in
      validate (pre', body, post) fv (modules_a, a::vars, structures, procs)
    end

and make_precondition params body global fv structures loc (modules, vars, _, procs) =
  (** Classify parameters *)
  let (structure_params, rest) = List.partition (fun x -> let x = Procedure.to_var x in Var.is_struct x && (not (Var.is_ptr x))) params in
  let (pointer_params, rest)   = List.partition (fun x -> let x = Procedure.to_var x in Var.is_ptr x) rest in (** All kinds of parameters *)
  (* let (array_params, ordinary_params) = List.partition (fun x ->
      match x with
        Block.ARRAY (_, _, _, _, _) -> true
      | _ -> false
     ) rest in *)
  (** deterministic by opportunity *)

  let refs, unrefs = classify_params [] pointer_params body in

  (* pn "REFS::";
  iterS (fun x -> p (Var.toStr (Procedure.to_var x))) "," refs;
  pn ""; *)
  let (body', i, exs) = (get_deterministic_parameter loc structures) |->> ((Block.SKIP, 0, []), refs @ structure_params) in
  (* let body' = (get_null_parameter loc structures) |->> (body', unrefs) in *) 
  (* let body' = Block.join body' structure_params in *)
  (* Block.pprint 1 body'; *)
  let entls1' = validate (global, body', []) fv (modules, vars, structures, procs) in
  let entls1' = snd |>>| entls1'  in
  let entls1 : (Formula.t * Formula.t) list = Formula.purify |>>| entls1' in
  
  let pp = (fun (ex, pures, pointers, preds) -> (ex @ exs, pures, pointers, preds)) |>>| (List.concat ((fun (p, _) -> p) |>>| entls1)) in 
  i, pp
(*  Block.join body' array_params, max, branches *)

*)