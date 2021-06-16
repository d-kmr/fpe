open VcpBase
open VcpTranslate
open Ftools
open Unix
module E = VcpElements
   
let fv = ref 0

module V = Map.Make(Bytes)

         

                
(** separation logic ++++++++++++++++++++++++++++++++++++++++++ *)
let new_log_var () =
  fv.contents <- !fv + 1;
  let sfv = string_of_int !fv in
  Exp.string_to_var ("t" ^ sfv ^ "'")

let term_subs (texp:Term.t) (var:Exp.var_t) (newv:Exp.var_t) : Term.t =
  let texp' = Term.substitute (Term.encode var) (Term.encode newv) texp in
  texp'

let false_bexp =
  let zero = Term.EXP (Exp.CONST 0) in
  BExp.UNIT (zero, Op.NE, zero)

let false_formula = [([], [false_bexp], [], [])]

let qvar () =
  let nv = Exp.set_question $$ new_log_var () in
  Term.EXP nv

let rec peano_to_pb e =
  match e with
    Term.NULL -> Term.NULL
  | Term.EXP e ->
     let _T e = Term.EXP e in
     let op o t1 t2 =
       match t1, t2 with
         (Term.EXP Exp.UNDEF), _ -> raise (StError "Unexpected UNDEF")
       | _, (Term.EXP Exp.UNDEF) -> raise (StError "Unexpected UNDEF")
       | Term.EXP e1, Term.EXP e2 -> _T (Exp.BINOP (e1, o, e2))
       | _, _ -> Term.NULL
     in
     let rec aux = function
       | Exp.BINOP (x, o, y) ->
          begin
            let x' = aux x in
            let y' = aux y in
            match o with
            | Op.MUL ->
               begin
                 match x', y' with
                   Term.EXP (Exp.CONST _), _
                 | _, Term.EXP (Exp.CONST _) -> op o x' y'
                 | _, _ -> qvar ()
               end
            | Op.DIV | Op.MOD ->
               begin
                 match x', y' with
                 | _, Term.EXP (Exp.CONST _) -> op o x' y'
                 | _, _ -> qvar ()
               end
            | Op.SHR ->
               begin
                 match x', y' with
                 | _, Term.EXP (Exp.CONST cy) ->
                     let py = Exp.power_2 cy in
                     op Op.DIV x' (Term.EXP (Exp.CONST py))
                 | _, _ -> qvar ()
               end
            | Op.SHL ->
               begin
                 match x', y' with
                 | _, Term.EXP (Exp.CONST cy) ->
                     let py = Exp.power_2 cy in
                     op Op.MUL x' (Term.EXP (Exp.CONST py))
                 | _, _ -> qvar ()
               end
            | Op.ADD | Op.SUB ->
              op o x' y'
            | _ -> qvar ()
          end
       | Exp.REF (e) ->
          _T Exp.UNDEF
       | Exp.LBL (lbl, e) ->
          _T Exp.UNDEF
       | Exp.SIZEOF (_tau) ->
          
          let sz = Exp.__size_by_name V.empty !E.all_struct _tau in
          _T sz
       | c -> _T c
     in
     let e' = aux e in
     e'

let has_question_in_term = function
    Term.NULL -> false
  | Term.EXP exp ->
     begin
       let rec aux = function
         | Exp.BINOP (x, o, y) ->
            begin
              let x' = aux x in
              let y' = aux y in
              x' || y'
            end
         | Exp.FCALL _ -> false
         | Exp.REF (e) ->
            aux e
         | Exp.LBL (lbl, e) ->
            aux e
         | Exp.VAR _ as v ->
            Exp.is_question v
         | Exp.UNDEF -> true
         | _ -> false
       in
       aux exp
     end

let rec reduce_size_of e =
  match e with
    Term.NULL -> Term.NULL
  | Term.EXP e ->
     let _T e = Term.EXP e in
     let rec aux = function
       | Exp.BINOP (x, o, y) ->
          begin
            let x' = aux x in
            let y' = aux y in
            Exp.BINOP (x', o, y')
          end
       | Exp.SIZEOF (_tau) ->
          let sz = Exp.__size_by_name V.empty !E.all_struct _tau in
          sz
       | c -> c
     in
     let e' = aux e in
     _T e'

let rec reduce_sizeof_b = function
    BExp.UNIT (t1, o, t2) ->
    let t1' = reduce_size_of t1 in
    let t2' = reduce_size_of t2 in
    BExp.UNIT (t1', o, t2')
  | BExp.OP (b1, o, b2) ->
     let b1' = reduce_sizeof_b b1 in
     let b2' = reduce_sizeof_b b2 in
     if b1' = BExp._T then
       if o = Op.AND then
         b2'
       else
         BExp._T
     else if b2' = BExp._T then
       if o = Op.AND then
         b1'
       else
         BExp._T
    else
      BExp.OP (b1', o, b2')
  | BExp.LBL (lbl, b) ->
     BExp._T
  | _ -> BExp.NOTHING
     
let rec peano_to_pb_b ?ignore_term:(ig=false) = function
    BExp.UNIT (t1, o, t2) ->
    let t1' = if ig then t1 else peano_to_pb t1 in
    let t2' = if ig then t2 else peano_to_pb t2 in
    if has_question_in_term t1' || has_question_in_term t2' then
      BExp._T
    else
      BExp.UNIT (t1, o, t2)
  | BExp.OP (b1, o, b2) ->
     let b1' = peano_to_pb_b b1 in
     let b2' = peano_to_pb_b b2 in
     if b1' = BExp._T then
       if o = Op.AND then
         b2'
       else
         BExp._T
     else if b2' = BExp._T then
       if o = Op.AND then
         b1'
       else
         BExp._T
    else
      BExp.OP (b1', o, b2')
  | BExp.LBL (lbl, b) ->
     BExp._T
  | _ -> BExp.NOTHING

let peano_to_pb_pointer (p, fields) =
  let p' = peano_to_pb p in
  (p', (fun (f, v) -> f, peano_to_pb v) |>>| fields)
  
let rec fve_of_exp e =
  match e with
    Exp.FCALL _ -> [Term.EXP e]
  | Exp.ADDR _ -> [Term.EXP e]
  | Exp.BINOP (x, o, y) ->
     begin
       let fve1 = fve_of_exp x in
       let fve2 = fve_of_exp y in
            match o with
            | Op.MUL ->
               begin
                 match x, y with
                   Exp.CONST _, _ -> fve1
                 | _, Exp.CONST _ -> fve2
                 | _, _ -> [Term.EXP e]
               end
            | Op.DIV | Op.MOD ->
               begin
                 match x, y with
                 | _, Exp.CONST _ -> fve1 
                 | _, _ -> Exp.pprint e; pn ""; [Term.EXP e]
               end
            | Op.SHR ->
               begin
                 match x, y with
                 | _, Exp.CONST _ ->
                    fve1
                 | _, _ -> [Term.EXP e]
               end
            | Op.SHL ->
               begin
                 match x, y with
                 | _, Exp.CONST _ ->
                    fve1
                 | _, _ -> [Term.EXP e]
               end
            | Op.ADD | Op.SUB ->
              fve1 @@ fve2
            | _ -> fve1 @@ fve2
          end
  | Exp.REF (_) ->
     [Term.EXP e]
  | Exp.LBL (lbl, _) ->
     [Term.EXP e]
  | _ -> []
  
let fve_of_term = function
    Term.NULL -> []
  | Term.EXP e -> fve_of_exp e
  
let rec fve_of_bexp = function
    BExp.UNIT (t1, _, t2) ->
    fve_of_term t1 @@ fve_of_term t2
  | BExp.OP (b1, _, b2) ->
     fve_of_bexp b1 @@ fve_of_bexp b2
  | _ -> []

let fve_of_pointer (t, data) =
  let fve1 = fve_of_term t in
  let fves = fve_of_term |>>| (snd |>>| data) in
  (@@) |->> (fve1, fves)

let fve_of_predicate (_, data) =
  (@@) |->> ([], fve_of_term |>>| data)
  
let peano_to_pb_formula ?ignore_term:(ig=false) (a,b,c,d) =
  let tobe1 = (@@) |->> ([], (fve_of_bexp |>>| b)) in
  let tobe2 = (@@) |->> ([], (fve_of_pointer |>>| c)) in
  let tobe3 = (@@) |->> ([], (fve_of_predicate |>>| d)) in
  let tobe = tobe1 @@ tobe2 @@ tobe3 in
  
  let tobe_qvar = (fun x -> x, qvar ()) |>>| tobe in
  dbg "SAT" "tobes: " (iterS (fun (t1,t2) -> Term.pprint t1; p "->"; Term.pprint t2) ",") tobe_qvar ;
  let b'' = BExp.par_subs tobe_qvar |>>| b in
  let b' = BExp.evals (reduce_sizeof_b |>>| (peano_to_pb_b ~ignore_term:ig |>>| b'')) in
  let c' = Pointer.par_subs tobe_qvar |>>| c in
  let d' = Predicate.par_subs tobe_qvar |>>| d in
  (a,b',c',d')

let rec count_disj = function
    BExp.UNIT (_,_,_) -> 0
  | BExp.OP (x, Op.AND, y) -> count_disj x + count_disj y
  | BExp.OP (x, Op.OR, y) -> 1 + count_disj x + count_disj y
  | _ -> 0

let list_to_ptr (a,b,c,d) =
  let d',d'' = List.partition (function ("List",_) -> true | _ -> false) d in
  let p' = (fun (_, data) ->
      match data with
        t::u::[] -> (t, [("*",u)])
      | _ -> raise Error
    ) |>>| d' in
  (a,b,c@p',d'')


let to_satchecker msec d =
  ConvFtoK.decide_ps_faisal_sat_pb d
  (* let is_done = ref false in
  let ret_val = ref false in
  begin
    match fork () with
      0 ->
       let res = (ConvFtoK.decide_ps_faisal_sat_pb d) in
       is_done := true;
       ret_val := res;
       ()
    | id ->
       let t1 = Sys.time () in
       while not !is_done do
         let t2 = Sys.time () in
         if (t2 -. t1) > msec then
           begin
             kill id 15;
             pn "SAT check is killed";
             ret_val := false;
             is_done := true
           end;
         if !is_done then
           begin
             pn "killing child process";
             kill id 15;
             is_done := true
           end;
         ignore (Unix.select [] [] [] 0.001);
         
       done
  end;
  
  !ret_val *)
;;
  
let check_sat2 (a,b,c,d) =
  (* let d = (function (_, (_::Term.EXP (Exp.CONST 0)::_)) -> false | (_, _) -> true) |>- d in *)
  dbg "SAT" "to check SAT (Original):\n" Formula.pprint [(a,b,c,d)];
  
  let b'' = (function BExp.LBL (_,_) -> false | _ -> true ) |>- b in
  let ((_,b',_,_) as form) = list_to_ptr $$ peano_to_pb_formula (a,b'',c,d) in
  
  dbg "SAT" "to check SAT:" Formula.pprint [form];
  begin
    let entl = ([form], false_formula) in
    (* Formula.pprint [form]; pn " TO BE CHECKED"; *)
    let t1 = Sys.time () in
    let ans = try (to_satchecker 2. [entl]) with e ->
                pn "Exception from Kimura's Sat checking.";
                Formula.upprint form;
                pn ""; raise e in
    let t2 = Sys.time () in
    dbg "PERF" "SAT time:" p (string_of_float (t2 -. t1));
    if ans then pn_s "SAT" "Sat" else pn_s "SAT" "Unsat";
    ans
  end

let biabd a' b =
  dot ();
  let t1 = Sys.time () in
  let a = (fun (p,q,r,s) -> (p,BExp.evals (reduce_sizeof_b |>>| (peano_to_pb_b ~ignore_term:true |>>| q)),r,s)) a' in

  dbg "BIABD" "sizeof reduced:\n:" Formula.upprint a;
  let res = try ConvFtoK.biabduction2 a b with e -> pn "Exception from Kimura's biabduction"; raise e in
  let t2 = Sys.time () in
  dbg "PERF" "BIABD time:" p (string_of_float (t2 -. t1));
  res

let formula_subs (formula : Formula.t) var newv =
  Formula.substitute (Term.encode var) (Term.encode newv) formula

let formula_subs_t formula var newv =
  Formula.substitute var newv formula (Locs.dummy)

(** Simp(Ex x. \/ A) = \/ (Ex x.A) *)
let ex (x:Exp.var_t) formula =
  let formula' = (fun (a, b, c, d) -> (Exp.var_to_str x::a, b, c, d)) |>>| formula in
  formula'

let eq var term : BExp.t =
  BExp.UNIT (Term.encode var, Op.EQ, term)

(** Simp(PI & Ex x.A) = Ex x.(PI & A) and Simp(PI & (A | B)) = (PI & A) | (PI & B) *)
let uconjunct (a, b, c, d) (bexp:BExp.t) =
  (a, [bexp] @@ b, c, d)

let conjunct (formula:Formula.t) (bexp:BExp.t) =
  (fun x -> uconjunct x bexp) |>>| formula

let disjunct (formula1: Formula.t) (formula2: Formula.t) =
  formula1 @ formula2

let uneg_conjunct bexp (a, b, c, d) =
  (a, BExp.complement bexp::b, c, d)

let neg_conjunct bexp formula =
  let formula' = (uneg_conjunct bexp) |>>| formula in
  formula'

let sep_conjunct pointer formula =
  let formula' = (fun (a, b, c, d) -> (a, b, pointer::c, d)) |>>| formula in
  formula'

let rec is_ptr_dangling ptr exs bexps =
  (** This function gets all x such that ptr=x or x=ptr and also separates all other bexp. *)
  let extract_bexps = function
      BExp.UNIT (a, Op.EQ, b) when Term.eq ptr a -> [b], []
    | BExp.UNIT (a, Op.EQ, b) when Term.eq ptr b -> [a], []
    | other -> [], [other]
  in
  (** If a ptr is a quantifier then check if it is dangling. *)
  if (Term.toStr ptr) |<- exs then
    let extracted = extract_bexps |>>| bexps in
    let (companions', others') = List.split extracted in
    (** companions are list of x such that ptr=x or x=ptr *)
    let companions = List.concat companions' in
    (** others are list of all those bexps that do not contain ptr *)
    let others = List.concat others' in
    (** Check all the companions are dangling as well. *)
    List.for_all (fun c -> is_ptr_dangling c exs others) companions
  else
    false

let rec unicat = function
    [] -> []
  | x::xs ->
     x @@ unicat xs
  
let rec fsym_in_exp = function
    (Exp.FCALL _) as e -> [e]
  | Exp.BINOP (e1, _, e2) ->
     fsym_in_exp e1 @@ fsym_in_exp e2
  | Exp.INDICES (l_e) ->
     unicat (fsym_in_exp |>>| l_e)
  | Exp.ADDR e ->
     [Exp.ADDR e]
  | Exp.REF e ->
     fsym_in_exp e
  | Exp.NEG e ->
     fsym_in_exp e
  | Exp.ARROW (e, _) ->
     fsym_in_exp e
  | Exp.LBL (_, e) ->
     fsym_in_exp e
  | _ -> []

let fsym_in_term = function
    Term.NULL -> []
  | Term.EXP e -> fsym_in_exp e

let rec fsym_in_bexp = function
    BExp.UNIT (t1, _, t2) ->
    fsym_in_term t1 @@ fsym_in_term t2
  | BExp.BLOCK (_, t) ->
     fsym_in_term t
  | BExp.LBL (_, b) ->
     fsym_in_bexp b
  | BExp.OP (b1, _, b2) ->
     fsym_in_bexp b1 @@ fsym_in_bexp b2
  | BExp.NOTHING -> []

let fsym_in_pointer (p, data) =
  fsym_in_term p @@ unicat (fsym_in_term |>>| (snd |>>| data))

let fsym_in_predicate (_, data) =
  unicat (fsym_in_term |>>| data)

let fsym_in_formula (_, bs, pts, prs) =
  unicat (fsym_in_bexp |>>| bs) @@ 
    unicat (fsym_in_pointer |>>| pts) @@
      unicat (fsym_in_predicate |>>| prs)

let elim_fsym (a,b) =
  let fsyms = unicat (fsym_in_formula |>>| a) @@ unicat (fsym_in_formula |>>| b) in

  iterS Exp.pprint ", " fsyms; pn "";
  let mp = (fun a -> (Term.EXP a, Term.EXP ((new_log_var ())))) |>>| fsyms in
  (Formula.par_subs mp a, Formula.par_subs mp b)
  
let entail_all opt formula formulas =
  let to_lastaddr (a,b,c,d) = (a,b,c,(fun (p,l) ->
                                 match p, l with
                                   "Array", ((Term.EXP st)::(Term.EXP ln)::_) ->
                                   ("Array", (Term.EXP st)::(Term.EXP (Exp.BINOP (st,Op.ADD,Exp.BINOP(ln,Op.SUB,Exp.CONST 1))))::[])
                                 | _ -> (p,l)
                               ) |>>| d) in
  let formula = to_lastaddr |>>| formula in
  let formulas = (fun f -> to_lastaddr |>>| f) |>>| formulas in
  
  let entail (pre, post) =
    try
      ConvFtoK.decide_ps_faisal_b [(pre, post)]
    with e ->
      pn "Exception from Kimura's entailment checking";
      iterS Formula.print "" pre; pn " |-";
      iterS Formula.print "" post;
      raise e
  in
  List.exists (fun rhs ->
      pf_s opt Formula.pprint formula;
      p_s opt "|-";
      pf_s opt Formula.pprint rhs; pn_s opt "";
      
      let x  = (entail (formula, rhs)) in
      if x then pn_s opt "VALID" else pn_s opt "INVALID"; pn_s opt "";
      x
    ) formulas


let entail opt pre post =
  let (pre', post') = elim_fsym ([pre], [post]) in
  entail_all opt pre' [post']

let rec rprint pre program =
  if !Options.to_be_report_printed then
    begin
    let (lbl, line) =
      match program with
        Block.SKIP ->
        "SK: ", ("", -1)
      | Block.ASSIGN (var, exp, program, l) ->
         "AS ", l
      | Block.IF (b, p1, p2, pr, l) ->
         "IF ", l
      | Block.WHILE (b, _, block, inv, body, l) ->
         "WH ", l
      | Block.CONS (exp, fields, pr, loc) ->
         "CO ", loc
      | Block.MUTATION (obj, fieldname, to_assign, pr, loc) ->
         "MU ", loc
      | Block.LOOKUP (var, obj, fieldname, pr, loc) ->
         "LU ", loc
      | Block.DISPOSE (obj, pr, loc) ->
         "DI ", loc
      | Block.MALLOC (a, tl, body, loc) ->
         "AR ", loc
      | _ -> "OT", ("", -1)
    in
    p "["; p (Locs.to_line line); p " "; p lbl; p "] : " ; Formula.pprint pre; pn "";
    end;;

let iunion (l1, u1) (l2, u2) =
  (Exp.min l1 l2, Exp.max u1 u2)

let iintersection (l1, u1) (l2, u2) =
  (Exp.max l1 l2, Exp.min u1 u2)

let formula_fvs formula = 
  List.concat ((fun (_,b,c,d) -> 
    (List.concat (BExp.fv |>>| b))  @@
      (List.concat (Pointer.fvs |>>| c))
) |>>| formula )


