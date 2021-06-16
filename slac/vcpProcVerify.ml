open VcpTranslate
open VcpBase
open Ftools

type filename = string
type fullpath = string
type funcname = string
type t_module = filename * fullpath * Global.t list * Structure.t list * bool * Formula.t
type t_buffer = Procedure.t * Formula.t option * Formula.t list option
type t_env = t_buffer list * string list * t_module list * int * Structure.t list


let check_immidiate_contradiction eqfs locs =
  let rec check_all maps = function
    | [] -> false
    | x::xs -> 
      match x with
      | BExp.UNIT (Term.EXP (Exp.CONST y), Op.EQ, Term.EXP (Exp.CONST z)) when y <> z -> true
      | BExp.UNIT (Term.EXP (Exp.VAR y), Op.NE, Term.NULL) -> not (Var.toStr y |<- locs) 
      | BExp.UNIT (Term.EXP (Exp.CONST y), Op.LE, Term.EXP (Exp.CONST z)) when y > z || y = z -> true
      | BExp.UNIT (x, Op.NE, y) -> x = y 
      | BExp.OP (y, Op.OR, z) -> (check_all maps [y]) && (check_all maps [z])
      | BExp.OP (y, Op.AND, z) -> check_all maps [y; z]
      | _ -> check_all maps xs
  in
  let v = check_all [] eqfs in
  v;;

let check_c (_, eqfs, ptr_list, _) =  
  (** a=b & A is equivalent to A[a:=b]. So *)
  let eqfs' = BExp.substitutes eqfs  eqfs in
  let ptr_list' = Pointer.substitutes ptr_list eqfs in
  let rec neq_f = function
      [] -> []
    |x::xs ->
      match x with
        BExp.UNIT(pt, Op.NE, Term.NULL) -> pt :: (neq_f xs)
      | _ -> neq_f xs
  in
  let is_any_not_null_invalid () =
    let neqs = neq_f eqfs in
    let is_any_not_null_no_ref = List.exists (fun x -> not(List.for_all (fun y -> match y with BExp.UNIT(y',Op.MAPSTO,_) -> x<>y' | _ -> true ) eqfs)) neqs in
    let is_any_not_null_no_ptr = List.exists (fun x -> not(List.for_all (fun (y,_) -> y <> x ) ptr_list)) neqs in
    is_any_not_null_no_ref || is_any_not_null_no_ptr
  in
  let is_pt_null = (List.exists (fun (pt,_) -> (pt = Term.NULL) || (pt = Term.EXP (Exp.CONST  0))) ptr_list') in
  let locs = Var.toStr |>>| (Term.decode |>>| (fst |>>| ptr_list')) in
  check_immidiate_contradiction eqfs' locs || is_pt_null || (is_any_not_null_invalid ())  ;;


let in_dim dim indices = true;;

let filter_global (a, eqs, b, c) fvs = 
  let eqs' = (fun x ->
      match x with
        BExp.UNIT (t1, _, t2) -> ((Term.toStr t1) |<- fvs) || ((Term.toStr t1) |<- fvs) 
      | _ -> false
    ) |>- eqs in
  (a, eqs', b, c);;



let rec check_refs vars = function
  | Block.SKIP -> vars
  | Block.ASSERT (_, p, _) -> check_refs vars p
  | Block.ASSIGN (_, e_term, p, _) ->
    let vars' = (Term.fv e_term) @@ vars in
    check_refs vars' p 
  | Block.IF (b, p1, p2, p, _) ->
    let vars = (BExp.fv b) @@ vars in
    let vars = check_refs vars p1 in
    let vars = check_refs vars p2 in
    check_refs vars p
  | Block.WHILE (b, p1, _, p, _) ->
    let vars = (BExp.fv b) @@ vars in
    let vars = check_refs vars p1 in
    check_refs vars p  
  | Block.PROCCALL (_, ps, p, _) -> check_refs vars p 
  | Block.CONS (e, _, p, _) -> check_refs vars p
  | Block.MUTATION (t1, _, t2, p, _) ->
    let vars = (Term.fv t1) @@ vars in
    check_refs vars p
  | Block.LOOKUP (v, t1, _, p, _) ->
    let vars = (Term.fv t1) @@ vars in
    check_refs vars p 
  | Block.DISPOSE (t, p, _) ->
    let vars = (Term.fv t) @@ vars in
    check_refs vars p 
  | Block.MAPS (v1, v2, p, _) -> check_refs vars p
  | Block.PARALLEL (p1, p2, p, _) ->
    let vars = check_refs vars p1 in
    let vars = check_refs vars p2 in
    check_refs vars p
  | Block.ARRAY (v, t, _, p, _) -> check_refs vars p


let get_precondition structures (proc : Procedure.t) ifv = function
    Some pre -> pre, ifv
  | None ->
    let (v_name, l_b_params, body) = proc in
    let l_v_params = Procedure.to_var |>>| l_b_params in
    (* let ptr_params = (fun v -> (v, false)) |>>| ((fun v -> Var.is_ptr v) |>- l_v_params) in *)
    let ref_params = check_refs [] body in 
    let pre, ifv = List.fold_left (fun (pre, ifv) v ->
        if Var.is_ptr v then
          if (Var.toStr v) |<- ref_params then
            if Var.is_struct v then
              let struct_name = Var.get_struct_name v in
              let fields = snd (List.find (fun (x, _) -> x = struct_name) structures) in
              let fields = (fun (n, e) -> (Bytes.concat "." n, e)) |>>| fields in
              Formula.add_to_spatial pre (Term.encode v, fields), ifv
            else
              (* let (aa, bb, c, d) = pre in *)
              let i = Formula.fresh_variable ifv in
              let si = Formula.i_to_v i in
              let (vi : Var.t) = Var.set_attributes (Var.toVar si) [Var.EXQ] in
              let eqf = BExp.UNIT (Term.encode v, Op.MAPSTO, Term.encode vi) in
              (fun (a,b,c,d) -> (si::a, eqf :: b, c, d)) |>>| pre, i 
          else
            (pre, ifv)
        else
          (pre, ifv)
      ) (Formula.empty, ifv) l_v_params in
    pre, ifv

let get_temp_postcondition structures proc = function
    Some l_post -> l_post
  | None -> 
    let (v_name, _, _) = proc in
    if Var.is_ptr v_name then
      if Var.is_struct v_name then
        let struct_name = Var.get_struct_name v_name in
        let fields = snd (List.find (fun (x, _) -> x = struct_name) structures) in
        let fields = (fun (n, e) -> (Bytes.concat "." n, e)) |>>| fields in
        let (_, attr) = v_name in
        [Formula.add_to_spatial Formula.empty (Term.encode ("$ret", attr), fields)]
      else
        [Formula.empty]
    else
      [Formula.empty]

(*
let update_vars vars var exp loc =
  let v = fst var in
  if not (List.exists (fun (w, _) -> w = v) vars) && (exp = Term.NULL || exp = Term.EXP Exp.NOTHING) then
    var::vars
  else if (Bytes.get v 0) = '.' then
    let attrs = Term.infer_attributes vars loc exp in
    (v, attrs)::vars
  else
    vars
*)

let is_in_stack stack proc_name =
  List.exists ((=) proc_name) stack

let rec update_proc_buf proc_name pre l_posts (proc_buf : t_buffer list) = function
    [] -> proc_buf
  | x :: xs ->
    let x' = 
    match x with
    | ((pname, a, b), Some pre', None) when Var.toStr pname = proc_name ->
      ((pname, a, b), Some pre', Some l_posts)
    | ((pname, a, b), None, Some post') when Var.toStr pname = proc_name ->
      ((pname, a, b), Some pre, Some post')
    | ((pname, a, b), None, None) when Var.toStr pname = proc_name ->
      ((pname, a, b), Some pre, Some l_posts)
    | _ -> x
    in
    update_proc_buf proc_name pre l_posts (proc_buf @ [x']) xs
      ;;

let rec post_global_construct (env : t_env) (formula : Formula.t) = function
    [] ->
    formula, env
  | (g : Global.t) :: gs ->
    begin
      let (proc_buf, proc_stack, modules, ifv, structures) = env in
      match g with
      | Global.STATEMENT (p) ->
        begin
          match validate env formula p with
            [], ifv -> 
            let env = (proc_buf, proc_stack, modules, ifv, structures) in
            post_global_construct env formula gs
          | (formula', _)::_, ifv ->
            let env = (proc_buf, proc_stack, modules, ifv, structures) in
            post_global_construct env formula' gs
        end
      | Global.PROC (proc, pre, post, _, loc) ->
        let pre = if pre = Formula.empty then None else Some pre in
        let post = if post = Formula.empty then None else Some [post] in
        let env = ((proc, pre, post) :: proc_buf, proc_stack, modules, ifv, structures) in
        post_global_construct env formula gs
      | _ ->
        post_global_construct env formula gs
    end

and validate env pre program : (Formula.t * Formula.t) list * int =  
  let (proc_buf, proc_stack, modules, ifv, structures) = env in
  if check_c |>>| pre then
    ([], ifv)
  else
    match program with
    | Block.SKIP ->
      ([(pre, Formula.empty)], ifv) | Block.ASSERT (formula, pr, _) -> 
      let entls, ifv = validate env formula pr in
      ((pre, formula)) :: entls , ifv
    | Block.ASSIGN (var, exp, program, l) ->
      (** Skip unitialized declaration *)
      if exp = Term.EXP Exp.NOTHING then
        validate env pre program
      else
        (** x=exp[x:=x'] & (PI & SIGMA)[x:=x'] *)
        let (pre', fv') = Formula.assign [] pre var exp ifv l in
        let env = (proc_buf, proc_stack, modules, fv', structures) in
        validate env pre' program
    | Block.CONS (e_v, ts, pr, l) ->                                            (** v is expected to be properly typed *)
        (** Get the head of pointer *)
      let v       =
        match e_v with
          Exp.VAR v -> v
        | Exp.BINOP(Exp.VAR v, _, _) -> v
        | _ -> raise SError
      in
      let (exq, eqs, ptrs, preds) = pre in    
      if Var.is_struct v || Var.is_array v then                                                   (** Redundant: already checked by compiler. *)
        begin
          let fv'     = Formula.fresh_variable ifv in
          let s_fv    = Formula.i_to_v fv' in
          let v_fv    = Var.toVar s_fv in
          let t_fv    = Term.encode (Var.set_attributes v_fv (Var.get_attributes v)) in
          let t_v     = Term.encode v in
          let pre'    = Formula.substitute t_v t_fv (s_fv::exq, eqs, ptrs, preds) l in 
          let pre''   = Formula.add_to_spatial pre' (t_v, ts) in                  (** CAUTION: dummy field is used *)
          let pre'''  = Formula.is_memory_leak eqs ptrs t_v pre'' pre l in
          let env     = (proc_buf, proc_stack, modules, fv', structures) in 
          validate env pre''' pr
        end
      else
        raise (StError ("Structure or Array expected"))
        (*          validate (pre, pr, post) fv (procs, vars, structures) *)
    | Block.LOOKUP (v, ((Term.EXP (Exp.VAR ptv)) as pt), "*", pr, l) ->
      let (exqs, eqs, ptrs, preds) = pre in 
      begin
        let ref = (fun x ->                                                     (** find what x points to... *)
            match x with
            | BExp.UNIT (y, Op.MAPSTO, z) when (* y = pt || *) Formula.(===) eqs y pt -> true 
            | _ -> false ) |>- eqs 
        in
        begin
          match ref with 
          | BExp.UNIT (_, _, exp) :: [] ->  
            validate env pre (Block.ASSIGN (v, exp, pr, l))            (** {A & pt=>z} v = z {B} |- {A & pt=>z} v = *pt {B} *)
          | _ ->
            (** It does not refer to any variable. So skip or show error if sure *)
            (* let _ = warn (" No reference of " ^ (Var.toStr ptv)) l () in *)
            validate env pre pr  
        end
      end
    | Block.LOOKUP (v, pt, "*", pr, l) ->
      validate env pre pr
    | Block.LOOKUP (v, pt, i, pr, l) ->                                        (** {A * pt->(i:v_t)} v = pt->i {B} |- {A * pt->(i:v_t)} v = v_t {B} *)
      let v_t = Formula.get_from pre pt i l in
      let (pre', fv') = Formula.assign [] pre v v_t ifv l in
      let env     = (proc_buf, proc_stack, modules, fv', structures) in
      validate env pre' pr
    | Block.MUTATION ((Term.EXP (Exp.VAR ptv)) as pt, "*", t, pr, l) ->        (** {A & pt=>z} z = t {B} |- {A & pt=>z} *pt = t {B} *)
      let (_, eqs, _, _) = pre in 
      let ref = (fun x ->
        match x with
        | BExp.UNIT (y, Op.MAPSTO, z) when y = pt -> true 
        | _ -> false ) |>- eqs 
      in
      begin
      match ref with
      | BExp.UNIT (_, Op.MAPSTO, Term.EXP (Exp.VAR exp)) :: [] -> 
        validate env pre (Block.ASSIGN (exp, t, pr, l))
      | _ -> 
        validate env pre pr
      end
    | Block.MUTATION (pt, i, t, pr, l) ->
      let pre = 
        match pt with
        | Term.EXP (Exp.BINOP (Exp.VAR array_name, Op.ADD, indices)) -> 
          let (a, b, c, d) = pre in
          if List.exists (fun x -> match x with BExp.BLOCK (n, dim) -> Var.eq n array_name && in_dim dim indices | _ -> false ) b &&
             not (List.exists (fun (n, _) -> n = pt) c) then
            (a, b, (pt, [("*", Term.NULL)])::c, d)
          else
            pre
        | _ -> pre
      in
      let pre' = Formula.set_to pre pt i t l in
      (* pw "MUTATION:"; (* Formula.pprint pre'; pn ""; *) *)
      validate env pre' pr
    | Block.DISPOSE (pt, pr, l) -> 
      let (_, eqs, _, _) = pre in
      Formula.new_ptr.contents <- (List.filter (fun x -> not (Formula.(===) eqs x pt)) !Formula.new_ptr);
      let pre' = Formula.delete_from pre pt l in
      (* pw "DISPOSE:"; (* Formula.pprint pre'; pn ""; *) *)
      validate env pre' pr
    | Block.IF (e, p1, p2, pr, _) -> 
      let pre1 = Formula.add_to_formula pre e in
      let pre2 = Formula.add_to_formula pre (BExp.complement e) in 
      (* pw "IF:"; (* Formula.pprint pre1; pw " AND"; Formula.pprint pre2; pn ""; *) *)
      let entls1, ifv1 = validate env pre1 (Block.compose pr p1) in
      let entls2, ifv2 = validate env pre2 (Block.compose pr p2) in
      let ifv = if ifv1 > ifv2 then ifv1 else ifv2 in
      entls1 @ entls2, ifv
    | Block.MAPS (_from, _to, body, l) -> 
      let (a, eqs, b, c) = pre in
      (** discard old reference of _from *)
      let (_, rest) = List.partition (fun x -> 
        match x with 
        | BExp.UNIT (y, Op.MAPSTO, _) -> y = (Term.encode _from) 
        | _ -> false) eqs 
      in  
      let exp = BExp.UNIT (Term.encode _from, Op.MAPSTO, Term.encode _to) in
      let eqs' = Formula.is_memory_leak eqs b (Term.encode _from) (exp::rest) rest l in
      validate env (a, eqs', b, c) body
    | Block.PARALLEL (pr1, pr2, pr, _) -> 
      let entls1, ifv1 = validate env pre  (Block.compose pr pr1) in
      let entls2, ifv2 = validate env pre  (Block.compose pr pr2) in
      let ifv = if ifv1 > ifv2 then ifv1 else ifv2 in
      entls1 @ entls2, ifv
    | Block.WHILE (b, block, (x,y,z,w), body, l) -> 
      if (x,y,z,w) = ([],[],[],[]) then 
        validate env pre (Block.IF (b, block, Block.SKIP, body, l))
      else
        let f = (x, b::y, z, w) in
        let f' = (x, (BExp.complement b)::y, z, w) in
        let ent1 = (pre, f) in
        let entl1, ifv1 = validate env f block (*, (x,y,z,w))*) in
        let entl2, ifv2 = validate env f' body in
        let ifv = if ifv1 > ifv2 then ifv1 else ifv2 in
        ent1::(entl1 @ entl2), ifv
    | Block.ARRAY (a, b, body, _) ->
      let (exqs, eqs, c, pred) = pre in
      let new_block = BExp.BLOCK (a, b) in
      let pre' = (exqs, new_block::eqs, c, pred) in
      validate env pre' body 
    | Block.PROCCALL (str, args, body, l) -> 
      let p_pre, p_posts =
        if List.exists (fun (((pn, _), _, _), _, _) -> pn = str) proc_buf then
          let env', p_pre, p_posts = verify_a_procedure env pre str in
          p_pre, p_posts
        else
          begin
            try
              let (the_module, _, _, _, _, _) = List.find (fun (_, _, l_globals, _, _, _) ->
                  List.exists (fun g ->
                      match g with
                        Global.PROC ((proc_name, _, _), _, _, _) -> (Var.toStr proc_name) = str
                    | _ -> false
                    ) l_globals) modules
              in
              let env, pre = load_module env the_module in
              pre, [pre] (** ??? *)
          with
            _ -> raise (StError ("Function not found"))
          end
      in   
(*      let subs_p_pre = substitute param args p_pre in
      let subs_p_posts = (substitute param args) |>>| p_posts in
      let extra_heap = subtract_heap pre p_pre in
      let comp_posts = (add_heap extra_heap) |>>| subs_p_posts in
        let entls, ifv = validate env comp_posts body in   
        (pre, subs_p_pre) :: entls, ifv *)
      (pre, p_pre) :: [] , ifv

(** 
   env = 
   procedure_buffer : list of procedures of loaded modules, 
   procedure_stack : list of procedures ever called,
   modules : all modules
   ifv : last fresh variable index
   structures : all loaded structures 
*)
and verify_a_procedure (env : t_env) precondition proc_name : t_env * Formula.t * Formula.t list =
  (** Decompose the environment *)
  let (proc_buf, proc_stack, modules, ifv, structures) = env in
  try
    (** Search the procedure in current buffer *)
    let (proc, o_pre, o_post) = List.find (fun ((fname, _, _), _, _) -> Var.toStr fname = proc_name) proc_buf in
    (** Get or construct the precondition *)
    let pre, ifv = get_precondition structures proc ifv o_pre in
    (** Get or construct the temporary postcondition *)
    (* let t_posts = get_temp_postcondition structures proc o_post in *)
    match o_post with
      None -> (** If there is no postcondition available *)
      (** If it is a recursion, treat differently *)
      if is_in_stack proc_stack proc_name then
        (** Should be changed later *)
        raise (StError ("Recursion detected"))
      else
        let (_, _, body) = proc in
        begin
          match validate env pre body with
            [], _ -> raise (StError ("Bug in procedure"))
          | (l_entls, ifv) ->
            let l_posts = List.fold_left (fun a (pr, po) -> if po = Formula.empty then pr::a else a) [] l_entls in
            let proc_buf = update_proc_buf proc_name pre l_posts [] proc_buf in
            let env = (proc_buf, proc_stack, modules, ifv, structures) in
            env, pre, l_posts
        end
    | Some l_posts ->
        let env = (proc_buf, proc_stack, modules, ifv, structures) in
        env, pre, l_posts
    with
    _ -> raise (StError ("Unusual search result"))

(** Returns updated env and global_precondition *)
and load_module (env : t_env) module_name : t_env * Formula.t =
  let (proc_buf, proc_stack, modules, ifv, structures) = env in
  match List.partition (fun (m_name, _, _, _, _, _) -> m_name = module_name) modules with
    ((_, path, l_globals, structs, _, _)::_), r_modules ->
    let pre, env = post_global_construct env Formula.empty l_globals in
    let (proc_buf, proc_stack, modules, ifv, structures) = env in
    (** Update the current module *)
    let modules = (module_name, path, l_globals, structs, true, pre) :: r_modules in
    let env = (proc_buf, proc_stack, modules, ifv, structures) in
    env, pre
  | _ -> raise (StError ("No module found: " ^ module_name))



(*
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
      end 
*)
                                    


       
    
    
    (*
    | Block.PROCCALL (str, args, body, l) ->
      begin
        match body with
          Block.ASSIGN (v1, e1, b1, l1) when l = l1 -> 
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
              let f_struct = List.filter (fun (n, _) -> n = type_name) (!Block.structures) in
              (* pn type_name;
                 pi (List.length f_struct); *)
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
                
            | true, false ->
              let nv = newvar () in
              let attr = Var.get_attributes v1 in
              let body = 
                Block.PARALLEL(
                  Block.ASSIGN (v1, Term.NULL, Block.SKIP, l),
                  Block.MAPS (v1, (nv, attr), Block.SKIP, l),
                  b1,
                  l)
              in validate (pre, body, post) fv packs
            | false, true ->
              let (_, fields) = List.find (fun (n, _) -> n = type_name) (!Block.structures) in
              let body = Block.CONS (Exp.VAR v1, (fun (ns, e) -> (Bytes.concat "." ns, e)) |>>| fields, Block.SKIP, l) in
              validate (pre, body, post) fv packs
            | false, false ->
              let nv = newvar () in
              let attr = Var.get_attributes v1 in
              let body = Block.ASSIGN (v1, Term.encode (nv, attr), Block.SKIP, l) in
              validate (pre, body, post) fv packs
          end
        | _ -> validate (pre, body, post) fv packs
      end

*)



