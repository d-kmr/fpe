open Ftools
open VcpBase
open VcpTranslate
module M = Map.Make(Exp)
module F = Map.Make(String)
module E = Smtsyntax.Exp
module S = Smtsyntax
module Z = Smttoz3
module V = Map.Make(Bytes)
module SatResult = Smttoz3.SatcheckResult
module EL = VcpElements

exception LibraryFunction
        
type t =
  | FAIL
  | SKIP of Locs.t
  | ASSIGN of Exp.t * Term.t * Locs.t
  | IF of BExp.t * t * t * Locs.t
  (* | CONS of Exp.t * (string * Term.t) list * Locs.t  (** Name, fields, rest *) *)
  | MUTATION of Term.t * Field.t * Term.t * Locs.t
  | LOOKUP of Exp.t * Term.t * Field.t * Locs.t
  | DISPOSE of Term.t * Locs.t
  | COMP of t * t * Locs.t
  | WHILE of BExp.t * BExp.t list * t * Locs.t
  | MALLOC of Exp.t * Exp.t * Locs.t (** Name, Length, rest *)
  | SARRAY of Exp.t * Term.t * (Exp.t * Term.t) list * Locs.t (** Name, Length, rest *)
  | PROCCALL of string * Term.t list * Locs.t
  | BLOCK of t list * t * Locs.t
  | DECL of Exp.t * Exp.t list * Block.init * Locs.t
  | RETURN of Term.t * Locs.t
  | LABEL of string * bytes list * Locs.t
;;

      
type d = BExp.t * BExp.t * BExp.t

type i = Term.t M.t * BExp.t list * Formula.ut
type s = Term.t M.t * Formula.ut * Formula.ut

type spec = Term.t * (Term.t M.t * BExp.t list * Formula.ut) * (Term.t M.t * BExp.t list * Formula.ut)
type specs = spec list * d
type fs = (Exp.attr list * Term.t list * specs * t) F.t

(* type ft = string * string * Exp.attr list * (Exp.t * Block.t list * Block.t) *)
type pck = string * fs * String.t list * Exp.t list * Structure.t V.t * EL.programs_t
(**
 * Store, Path, Postcondition, Inferred Precondition, new variables
 *)
type o = Term.t M.t * BExp.t list * Formula.ut * Formula.ut * Exp.t list * (Term.t M.t) F.t
type r = Term.t * Term.t M.t * BExp.t list * Formula.ut * Formula.ut

type interval_I = Exp.t * Exp.t
type intervals_J = interval_I list

type flag = PRE | POST | MOD

exception Timeout of string
exception PrecondFails of string
exception MemoryUnsafe

let all_struct = ref V.empty

let empty = ([],[],[],[])

let loop = ref 0;;

let start_t = ref 0.0;;

let all_functions : string list ref = ref [];;

let f_counter = ref 10000000000;;

let f_heap = ref F.empty;;

let current_function = ref "";;

let add_f f =
  let c = !f_counter in
  let _ = f_counter.contents <- c+1 in
  let tc = (Term.EXP (Exp.CONST c)) in
  let _ = f_heap.contents <- F.add f tc !f_heap in
  tc

let tmo msg x y =
  let t = Sys.time () in
  if !Options.timeout = 0.0 || (t -. !start_t) < !Options.timeout then
    x
  else
    begin
      raise (Timeout msg)
    end

let m_print_s s =
  p "[";
  M.iter (fun key value -> Exp.pprint key; p " = "; Term.pprint value; pw ",") s;
  p "]"
let m_print opt s =
  if opt |<- !Ftools.p_opt then
    begin
      p "[";
      M.iter (fun key value -> Exp.pprint key; p " = "; Term.pprint value; pw ",") s;
      p "]"
    end;;

let print_post opt s d a b l =
  if opt |<- !Ftools.p_opt then
    begin
      pn (Locs.to_str l);
      p "S:";
      m_print opt s;
      if List.length d > 0 then
        (p "\nd:";
         iterS BExp.pprint " & " d;
        )
      else
        p "\nd: True";
      p "\nA: ";
      Formula.pprint [a];
      p "\nB: ";
      Formula.pprint [b];
      pn "\n"
    end;;

let print_ret opt r s d a b =
  p "r:";
  Term.pprint r;
  p ", S:";
  m_print opt s;
  if List.length d > 0 then
    (p "\nd:";
     iterS BExp.pprint " & " d;
    )
  else
    p "\nd: True";
  p "\nA: ";
  Formula.pprint [a];
  p "\nB: ";
  Formula.pprint [b];
  pn "\n"
;;

let print_rets opt fn _X =
  pn_s opt fn;
  iterS (fun (r,s,d,a,b) -> print_ret opt r s d a b) "\n" _X;;
  
let pprint_f lbl (a,b,c,d,_,_) l =
  print_post lbl a b c d l

let print_pre opt s d a l =
  if opt="" || opt |<- !Ftools.p_opt then
    begin
      p (Locs.to_str l);
      p "\nS:";
      m_print opt s;
      if List.length d > 0 then
        (p "\nd:";
         iterS BExp.pprint " & " d
        )
      else
        p "\nd: True";
      p "\nA: ";
      Formula.pprint [a];
      pn "\n"
    end;;

let getLoc = function
    ASSIGN (_, _, l)
  | IF (_, _, _, l)
    | COMP (_, _, l)
    (* | CONS (_, _, l) *)
    | MALLOC (_, _, l)
    | SARRAY (_, _, _, l)
    | LOOKUP (_, _, _, l)
    | MUTATION (_, _, _, l)
    | DISPOSE (_, l)
    | WHILE (_, _, _, l)
    | PROCCALL (_, _, l)
    | BLOCK (_, _, l)
    | DECL (_, _, _, l)
    | RETURN (_, l)
    | LABEL (_,_,l)
    | SKIP l -> l
  | FAIL -> Locs.dummy

(** Print result *)
let print_them n x _P =
  List.iter (fun (s, d, a, b, _, _) -> print_post n s d a b (getLoc _P)) x

let msg tag m c =
  pn_s tag m;
  c;;

let substitute_all f sigma x = (fun x (to_be, by) -> f to_be by x) |->> (x, sigma)


let exp_to_smt_exp exp =
  let module E = Smtsyntax.Exp in
  let rec aux = function
      Exp.VAR (v, attr) -> E.Var (Exp.get_str (v, attr))
    | Exp.CONST (i) -> E.Int i
    | Exp.BINOP (e1, op, e2) -> E.App (Op.smt_print op, [aux e1; aux e2])
    | Exp.FCALL (s, ts) -> Smtsyntax.Exp.Var "smt_of_fcall"
    | _ -> E.Int 0
  in
  aux exp

let term_to_smt_exp = function
    Term.NULL -> Smtsyntax.Exp.Var "nil"
  | Term.EXP x -> exp_to_smt_exp x


                             
let bexp_to_smt_exp bexp =
  let module E = Smtsyntax.Exp in
  let rec aux = function
    | BExp.OP (e1, op, e2) -> E.App (Op.smt_print op, [aux e1; aux e2])
    | BExp.UNIT (e1, op, e2) -> E.App (Op.smt_print op, [term_to_smt_exp e1; term_to_smt_exp e2])
    | _ -> E.App ("and", [])
  in
  aux bexp

let rec exp_from_smt_exp exp =
   let module E = Smtsyntax.Exp in
   let rec aux = function
       E.Int x -> Exp.CONST x
     | E.Var x -> Exp.VAR (x, [])
     | E.App ("Ifz", xs) ->
        Exp.INDICES (exp_from_smt_exp |>>| xs)
     | E.App (op, a::bs) ->
        begin
          let oop = match op with
              "+" -> Op.ADD
            | "-" -> Op.SUB
            | "*" -> Op.MUL
            | "/" -> Op.DIV
            | _ -> Op.ADD
          in
          let ex =
            match bs with
              [b] ->
              Exp.BINOP (aux a, oop, aux b)
            | _ ->
              Exp.BINOP (aux a, oop, aux (E.App (op, bs)))
          in
          ex
        end
     | _ -> Exp.CONST 0
   in
   aux exp

  let bexp_from_smt_exp exp =
   let module E = Smtsyntax.Exp in
   let to_t x = Term.EXP (exp_from_smt_exp x) in
   let rec aux = function
       E.App ("=", a::b::_) ->
       BExp.UNIT (to_t a, Op.EQ, to_t b)
     | E.App (">=", a::b::_) ->
       BExp.OP (BExp.UNIT(to_t b, Op.LE, to_t a), Op.OR, BExp.UNIT (to_t a, Op.EQ, to_t b))
     | E.App ("<=", a::b::_) ->
       BExp.OP (BExp.UNIT(to_t a, Op.LE, to_t b), Op.OR, BExp.UNIT (to_t a, Op.EQ, to_t b))
     | E.App ("<", a::b::_) ->
       BExp.UNIT (to_t a, Op.LE, to_t b)
     | E.App (">", a::b::_) ->
       BExp.UNIT (to_t b, Op.LE, to_t a)
     | E.App ("not", a::_) ->
       BExp.complement (aux a)
     | E.App ("or", a::bs) ->
        (fun a b -> BExp.OP (a, Op.OR, aux b)) |->> (aux a, bs)
     | E.App ("and", a::bs) ->
        (fun a b -> BExp.OP (a, Op.AND, aux b)) |->> (aux a, bs)
     | _ -> BExp._F
   in
   aux exp
;;



(*
let rec decls program =
  match program with
  | Block.SKIP -> ([], Block.SKIP)
  | Block.ASSIGN (var, exp, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.ASSIGN (var, exp, pr', l))
  | Block.IF (b, p1, p2, pr, l) ->
     let (_, p1') = decls p1 in
     let (_, p2') = decls p2 in
     let (dcl, pr') = decls pr in
     (dcl, (Block.IF (b, p1', p2', pr', l)))
  | Block.WHILE (b, bs, block, inv, pr, l) ->
     let (_, block') = decls block in
     let (dcl, pr') = decls pr in
     (dcl, Block.WHILE (b, bs, block', inv, pr', l))
  | Block.CONS (exp, fields, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.CONS (exp, fields, pr', l))
  | Block.MUTATION (obj, fieldname, to_assign, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.MUTATION (obj, fieldname, to_assign, pr', l))
  | Block.LOOKUP (var, obj, fieldname, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.LOOKUP (var, obj, fieldname, pr', l))
  | Block.DISPOSE (obj, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.DISPOSE (obj, pr', l))
  | Block.PROCCALL (a, b, pos, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.PROCCALL (a, b, pos, pr', l))
  | Block.MALLOC (a,c,pr,l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.MALLOC(a,c,pr',l))
  | Block.SARRAY (a,b,c,pr,l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.SARRAY(a,b,c,pr',l))
  | Block.BLOCK (p, pr, l) ->
     let (dcl, pr') = decls pr in
     
     (dcl, Block.BLOCK (p, pr', l))
  | Block.DECL (v, len, data, pr, l) ->
     let (dcl, pr') = decls pr in
     (* if List.length len = 0 then
       match data with
         Block.INIT_E ->
         ((v,len,data,l)::dcl, pr')
       | Block.INIT_S tdata ->
          ((v,len,Block.INIT_E,l)::dcl, Block.ASSIGN (v, tdata, pr', l))
       | Block.INIT_M _ ->
          ()
     else *)
     ((v,len,data,l)::dcl, pr')
  | Block.RETURN (v, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.RETURN (v, pr', l))
  | Block.BREAK (pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.BREAK (pr', l))
  | Block.CONTINUE (pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.CONTINUE (pr', l))
  | Block.LABEL (lbl, el, pr, l) ->
     let (dcl, pr') = decls pr in
     (dcl, Block.LABEL (lbl, el, pr', l))
  | x -> ([], x)
      *)

let rec blocks program =

  match program with
  | Block.SKIP -> Block.SKIP
  | Block.ASSIGN (var, exp, pr, l) ->
     let pr' = blocks pr in
     Block.ASSIGN (var, exp, pr', l)
  | Block.IF (b, p1, p2, pr, l) ->
     let p1' = blocks p1 in
     let p2' = blocks p2 in
     let pr' = blocks pr in
     Block.IF (b, p1', p2', pr', l)
  | Block.WHILE (b, bs, block, inv, pr, l) ->
     let block' = blocks block in
     let pr' = blocks pr in
     Block.WHILE (b, bs, block', inv, pr', l)
  | Block.CONS (exp, fields, pr, l) ->
     let pr' = blocks pr in
     Block.CONS (exp, fields, pr', l)
  | Block.MUTATION (obj, fieldname, to_assign, pr, l) ->
     let pr' = blocks pr in
     Block.MUTATION (obj, fieldname, to_assign, pr', l)
  | Block.LOOKUP (var, obj, fieldname, pr, l) ->
     let pr' = blocks pr in
     Block.LOOKUP (var, obj, fieldname, pr', l)
  | Block.DISPOSE (obj, pr, l) ->
     let pr' = blocks pr in
     Block.DISPOSE (obj, pr', l)
  | Block.PROCCALL (a, b, pos, pr, l) ->
     let pr' = blocks pr in
     Block.PROCCALL (a, b, pos, pr', l)
  | Block.MALLOC (a,c,pr,l) ->
     let pr' = blocks pr in
     Block.MALLOC(a,c,pr',l)
  | Block.SARRAY (a,b,c,pr,l) ->
     let pr' = blocks pr in
     Block.SARRAY(a,b,c,pr',l)
  | Block.BLOCK (p, pr, l) ->
     let p' = blocks p in
     let pr' = blocks pr in
     Block.BLOCK (p', pr', l)
  | Block.DECL (v, len, data, pr, l) ->
     let pr' = blocks pr in
     let res = Block.BLOCK (Block.DECL (v, len, data, pr', l), Block.SKIP, l) in     
     res
  | Block.RETURN (v, pr, l) ->
     let pr' = blocks pr in
     Block.RETURN (v, pr', l)
  | Block.BREAK (pr, l) ->
     let pr' = blocks pr in
     Block.BREAK (pr', l)
  | Block.CONTINUE (pr, l) ->
     let pr' = blocks pr in
     Block.CONTINUE (pr', l)
  | Block.LABEL (lbl, el, pr, l) ->
     let pr' = blocks pr in
     Block.LABEL (lbl, el, pr', l)
  | x -> x



       
let rec toT' program =
  let wrap program pr l : t =
    if pr = Block.SKIP then
      program
    else
      COMP (program, toT' pr, l)
  in
  let program' =
    match program with
    (*  | Block.SKIP -> SKIP (Locs.dummy) *)
    | Block.ASSIGN (var, exp, pr, l) ->
       wrap (ASSIGN (var, exp, l)) pr l
    | Block.IF (b, p1, Block.SKIP, pr, l) ->
       let p1' = toT' p1 in
       wrap (IF (b, p1', SKIP l, l)) pr l
    | Block.IF (b, p1, p2, pr, l) ->
       wrap (IF (b, toT' p1, toT' p2, l)) pr l
    | Block.WHILE (b, bs, block, inv, pr, l) ->
       wrap (WHILE (b, bs, toT' block, l)) pr l
    | Block.CONS (exp, fields, pr, l) ->
       let fields' = (fun (a,b) -> (a,b)) |>>| fields in
       wrap (SARRAY (exp, Term.EXP (Exp.CONST 1), fields', l)) pr l
    | Block.MUTATION (obj, fieldname, to_assign, pr, l) ->
       wrap (MUTATION (obj, fieldname, to_assign, l)) pr l
    | Block.LOOKUP (var, obj, fieldname, pr, l) ->
       wrap (LOOKUP (var, obj, fieldname, l)) pr l
    | Block.DISPOSE (obj, pr, l) ->
       wrap (DISPOSE (obj, l)) pr l
    | Block.PROCCALL (a, b, _, pr, l) ->
       begin
         (* match a with
         | Term.EXP ((Exp.VAR _) as v) when Exp.is_funcptr v || Exp.is_ptr v ->
            (* pw "Possible Function Pointer Call: "; Term.pprint a; pn ""; *)
            wrap (PROCCALL (Term.toStr a, b, l)) pr l
         | Term.EXP (Exp.VAR _) ->
            wrap (PROCCALL (Term.toStr a, b, l)) pr l
         | _ -> *)
            (* pw "Possible Function Pointer Call: "; Term.pprint a; pn ""; *)
            wrap (PROCCALL (Term.toStr a, b, l)) pr l
       end
    | Block.MALLOC (a,c,d,l) ->
       wrap (MALLOC(a,c,l)) d l
    | Block.SARRAY (a,b,c,d,l) ->
       wrap (SARRAY(a,b,c,l)) d l
    | Block.SKIP ->
       SKIP (Locs.dummy)
    | Block.BLOCK (p, pr, l) ->
       (* let (dcls, p') = decls p in
       let dcls' = (fun (v,len,data,l) -> DECL (v,len,data,l)) |>>| dcls in *)
       begin
         let p' = toT' p in
         let p'' =
           match p' with
             COMP ((DECL (a,b,c,d) as decl), pr2, l2) ->
              begin
                match pr2 with
                  BLOCK (decls, pr3, l3) ->
                  BLOCK (decl::decls, pr3, l3)
                | _ ->
                   BLOCK ([decl], pr2, l)
              end
           | BLOCK (decls, pr2, l2) ->
              p'
           | _ ->
              BLOCK ([], p', l)
         in
         wrap p'' pr l
       end
    | Block.DECL (v, len, data, pr, l) -> wrap (DECL (v, len, data, l)) pr l
    | Block.RETURN (v, pr, l) -> wrap (RETURN (v, l)) pr l
    | Block.BREAK (pr, l) -> SKIP l
    | Block.CONTINUE (pr, l) -> SKIP l
    | Block.LABEL (lbl, el, pr, l) -> wrap (LABEL (lbl, el, l)) pr l
    | Block.FAIL -> FAIL
    | x ->
       Block.pprint 0 x;
       raise (StError "Program conversion error")
  in
  (*  p "%"; pn (Locs.to_str (getLoc program')); *)
  program'

let pprint body =
  let rec pprint' tab = function
      ASSIGN (a, b, lc) ->
       pt "" tab;
       Exp.pprint a;
       p " = ";
       Term.pprint b;
       pn ";"
    | IF (b, p1, p2, l) ->
       begin
         let tb = match p1 with BLOCK _ -> tab | _ -> tab+1 in
         let tc = match p2 with BLOCK _ -> tab | _ -> tab+1 in
         pt "if(" tab; BExp.pprint b; pn ")"; pprint' tb p1; 
         begin
           match p2 with
             BLOCK (_, SKIP _, _) -> pt "\n" tab
           | _ ->
              pt "else\n" tab; pprint' tc p2
         end;
       end
  | COMP (p1, p2, l) -> pprint' tab p1;   pprint' tab p2
  | MALLOC (v, t, l) -> pt "" tab; Exp.pprint v; p " = MALLOC("; Exp.pprint t; pn ")";
  | SARRAY (a, b, _, l) -> pw " SARRAY"; Exp.pprint a; pw ""; Term.pprint b
  | LOOKUP (a, _, _, l) -> pt "" tab; p " LOOKUP("; Exp.pprint a; pw ")"; pn ""
  | MUTATION (a, _, _, l) -> pt "" tab; p " MUTATION("; Term.pprint a; pw ")"; pn ""
  | DISPOSE (_, l) -> pt " DISPOSE" tab; pn ""
  | WHILE (_, _, _, l) -> pt " WHILE" tab; pn ""
  | SKIP _ -> pt "SKIP" tab; pn ""
  | PROCCALL (f,args,_) -> pt "PROC(" tab; p f; p ",["; iterS Term.pprint ";" args; pn "])"
  | BLOCK (ds, p1, _) ->
     pt "{" tab; pn ""; iterS (pprint' (tab+1)) "" ds; pprint' (tab+1) p1; pt "}" tab; pn ""   
  | DECL (a, len, init_data, lc) ->
     pt "decl " tab;
     
     (if Exp.is_struct a then
        let st = Exp.get_struct_name a in
        pw st;
        if Exp.is_ptrptr a then
          pw "**"
        else if Exp.is_ptr a then
          pw "*");
     if Exp.is_funcptr a && not (Exp.is_func a) then( p "(*"; Exp.pprint a; p ")") else Exp.pprint a;
     if List.length len > 0 then
       (p "["; iterS Exp.pprint "-" len; p "]");
     if init_data <> Block.INIT_E then p " = ";
     Block.print_init init_data;
     pw ";  //"; pn (Locs.to_str lc)
  | RETURN (t, _) -> pt "RETURN " tab; Term.pprint t; pn ""
  | LABEL (_, _, _) -> pt "LABEL" tab; pn ""
  | FAIL -> pt "FAIL" tab; pn ""
  in
  pprint' 0 body

  
let toT is_global program =
  if is_global then
    toT' program
  else
    begin
      let program' = blocks program in
      (* pn "Translated\n=============";
      Block.pprint 2 program'; *)
      let res = toT' program' in
      (* pn "Block Removed\n=============";
      pprint res; *)
      res
    end
;;
  

let neg b = BExp.complement b

let rec intersection xs = function
    [] -> []
  | (y::ys) ->
     if y |<- xs then
       y::intersection xs ys
     else
       intersection xs ys

let sepconj (a, b, c, d) (a1, b1, c1, d1) = (a @@ a1, b @@ b1, c @ c1, d @ d1)

let sepconj_cell formula cell = sepconj formula ([], [], [cell], [])

let sepconj_pred formula pred = sepconj formula ([], [], [], [pred])

let rec split3 = function
    []           -> [], [], []
  | ((a,b,c)::xs) -> let (ax, bx, cx) = split3 xs in (a::ax, b::bx, c::cx)

let fst3 (x, _, _) = x

let snd3 (_, x, _) = x

let trd3 (_, _, x) = x

let fst4 (x, _, _, _) = x

let _T x = Term.EXP x

let _TT = Term.encode

let __E (x, y) = Exp.VAR (x, y)

let __V = Exp.var

let __N x = fst $$ __V x

let _MakeArray_ptr (ptr, _) = ("Array", [ptr;ptr])
let _MakeArray_pred (_, data) = ("Array", data)
let _MakeArray (a,b,c,d) = (a,b,[],(_MakeArray_ptr |>>| c) @ (_MakeArray_pred |>>| d))

let newvar attr : Exp.t =
  let v = VcpVBase.new_log_var () in
  Exp.set_attributes v attr

(* let compare a b =
  let la = Bytes.length a in
  let lb = Bytes.length b in
  let rec aux i =
    
  in
 *)

let get_var_from_param fname = function
  | Block.ASSIGN (var, _, _, _)
    | Block.CONS (Exp.VAR _ as var, _, _, _) -> var
  | Block.MALLOC (var, _, _, _) -> var
  | Block.MUTATION (obj, fieldname, to_assign, pr, l) -> Term.toExp obj
  | Block.LOOKUP (var, obj, fieldname, pr, l) -> var
  | Block.SARRAY (var,b,c,d,l) -> var
  | Block.DECL (var, _, _, _, _) -> var
  | e -> __E ("GLOBAL", [])

       
let _PutVarAddr _A _x _t =
  let amp_x = Term.EXP (Exp.ADDR _x) in
  let (exs,pures,ptrs,preds) = _A in
  let matched, unmatched = List.partition (fun (x,_) -> x = amp_x) ptrs in
  match matched with
    [] -> _A
  | _ -> (exs, pures, (amp_x,[("*",_t)])::unmatched, preds)

let field_concat fields1 fields2 =
  if fields1 = [] then
    fields2
  else if fields2 = [] then
    fields1
  else
    let fns1 = fst |>>| fields1 in
    let fields2' = List.filter (fun (fn, fd) -> not (fn |<- fns1)) fields2 in
    fields1 @ fields2'

let pointer_merge (p1, fields1) (p2, fields2) =
  if Term.toStr p1 = Term.toStr p2 then
    begin
      [(p1, field_concat fields1 fields2)]
    end
  else
    [(p1, fields1); (p2, fields2)]

let pointer_concat (pointers1 : string list * Pointer.t list) (pointers2: string list * Pointer.t list) : string list * Pointer.t list =
  if snd pointers1 = [] then
    pointers2
  else if snd pointers2 = [] then
    pointers1
  else
    let rec aux ((p, fs):Pointer.t) (aa:Pointer.t list) =
      match aa with
        [] -> [(p, fs)]
      | ((pa, fsa)::a) ->
         if p = pa then
           (pa, field_concat fs fsa) :: a
         else
           (pa, fsa)::aux (p, fs) a
    in
    (fun ((exs, a)) p -> (exs @@ fst pointers2, aux p a)) |->> (pointers1, snd pointers2)

let rec list_to_disj = function
    [] -> BExp._T
  | [b] -> b
  | b::bs -> BExp.(b |. (list_to_disj bs))


let _Letter x = BExp.(x =/ Term.zero)

let _Tilde s = M.map (fun k v -> BExp.(k == v)) s


let rec eval' s = function
    Term.NULL -> Term.NULL
  | Term.EXP e ->
     let op o t1 t2 =
       match t1, t2 with
         Term.EXP e1, Term.EXP e2 -> _T (Exp.eval $$ Exp.BINOP (e1, o, e2))
       | _, _ -> Term.NULL
     in
     let rec e_eval = function
       | Exp.UNDEF -> _T Exp.UNDEF
       | Exp.NOTHING -> _T Exp.NOTHING
       | Exp.FCALL (s,ts) -> _T (Exp.FCALL (s, Term.toExp |>>| (e_eval |>>| ts)))
       | (Exp.VAR v) as ev ->
          begin
            (* if Exp.is_question v then
              Term.encode v
            else *) if M.mem ev s then
              M.find ev s
            else
              let v' = Exp.set_hat ev in
              _T v'
          end
       | Exp.BINOP (x, o, y) ->
          let x' = e_eval x in
          let y' = e_eval y in
          (op o x' y')
       | Exp.REF (e) ->
          begin
            let e' = e_eval e in
            match e' with
              Term.EXP e'' ->
               (*
              begin
                let (_,_,ptrs,_) = _A in
                try
                  let (pt, dt) = List.find (fun (pt, _) -> pt = e') ptrs in
                  snd (List.hd dt)
                with
                  _ -> _T (Exp.REF e'')
              end *)
               Term.EXP (Exp.REF e'')
            | _ -> raise (NullPointerException (Exp.toStr e))
          end
       | Exp.INDICES e ->
          let e' = e_eval |>>| e in
          begin
            match e' with
              [] -> Term.EXP (Exp.CONST 0)
            | x::xs -> ((fun a b -> op Op.MUL a b) |->> (x, xs))
          end
       | Exp.ADDR e ->
          let se = Exp.toStr e in
          if se |<- !all_functions then
            e_eval e
          else
            _T (Exp.ADDR e) (** Temporary Implementation *)
       | c -> _T c
     in
     e_eval e

let rec eval_b' _L (s : Term.t M.t) = function
    BExp.UNIT (t1, o, t2) -> BExp.unit (eval' s t1) o (eval' s t2)
  | BExp.OP (b1, o, b2) -> BExp.op (eval_b' _L s b1) o (eval_b' _L s b2)
  | BExp.LBL (lbl, b) ->
     begin
       try
         let _s' = F.find lbl _L in
         eval_b' _L _s' b
       with
         _ ->
         BExp._T
     end
  | _ -> BExp.NOTHING
;;

let not_same_set xs ys =
  let (xs', ys') = drop_common xs ys in
  List.length xs' > 0 || List.length ys' > 0
;;

       
let not_same_spatial ((_, _, ptrX1, predX1), (_, _, ptrY1, predY1)) ((_, _, ptrX2, predX2), (_, _, ptrY2, predY2)) =
  not_same_set ptrX1 ptrX2 || not_same_set predX1 predX2 || not_same_set ptrY1 ptrY2 || not_same_set predY1 predY2
;;

let rec reduce_biabd_result = function
    [] -> []
  | x::xs ->
     let xs' = not_same_spatial x |>- xs in
     x::reduce_biabd_result xs'
;;


let contains_no_undef_in_term t = not (VcpVBase.has_question_in_term t)

let rec contains_no_undef_in_bexp = function
    BExp.UNIT (t1, _, t2) -> contains_no_undef_in_term t1 && contains_no_undef_in_term t2
  | BExp.OP (b1, _, b2) -> contains_no_undef_in_bexp b1 && contains_no_undef_in_bexp b2
  | _ -> true

let rec is_linear ?in_terms:(constants=[]) exp =
  match exp with
    Exp.UNDEF -> true
  | Exp.VAR _ -> true
  | Exp.CONST _ -> true
  | Exp.STRING _ -> true
  | Exp.NEG t ->
     is_linear t
  (*  | Exp.BINOP (x, _, y) ->
     is_linear x && is_linear y *)
  | Exp.BINOP (x, Op.ADD, y)
    | Exp.BINOP (x, Op.SUB, y) ->
     is_linear x && is_linear y
  | Exp.BINOP (x, Op.MUL, Exp.CONST c)
    | Exp.BINOP (Exp.CONST c, Op.MUL, x) ->
     is_linear x
  | Exp.BINOP (x, Op.MUL, y) ->
     (y |<- constants && is_linear x) || (x |<- constants && is_linear y)
  | Exp.FCALL (s,ts) -> true
  | _ -> false

let is_term_linear ?in_terms:(constants=[]) = function
    Term.NULL -> true
  | Term.EXP e -> is_linear ~in_terms:constants e

let rec is_bexp_linear ?in_terms:(constants=[]) = function
    BExp.UNIT (x, op, y) ->
     let x' = is_term_linear ~in_terms:constants x in
     let y' = is_term_linear ~in_terms:constants y in
     x' && y'
  | BExp.OP (x, op, y) ->
     let x' = is_bexp_linear ~in_terms:constants x in
     let y' = is_bexp_linear ~in_terms:constants y in
     x' && y'
  | x -> false

let rec simplify_nonlinear ?in_terms:(constants=[]) = function
    BExp.UNIT (x, op, y) as b ->
     let x' = is_term_linear ~in_terms:constants x in
     let y' = is_term_linear ~in_terms:constants y in
     if x' && y' then
       b
     else
       BExp._T
  | BExp.OP (x, op, y) ->
     let x' = simplify_nonlinear ~in_terms:constants x in
     let y' = simplify_nonlinear ~in_terms:constants y in
     if x' = BExp._T then
       y'
     else if y' = BExp._T then
       x'
     else
       BExp.OP (x', op, y')
  | x -> x

let rec linear_exp ?in_terms:(constants=[]) exp =
  match exp with
    Exp.UNDEF -> Term.toExp (VcpVBase.qvar ())
  | Exp.VAR _ -> exp
  | Exp.CONST _ -> exp
  | Exp.STRING _ -> exp
  | Exp.NEG t ->
     Exp.NEG (linear_exp ~in_terms:constants t)
  | Exp.BINOP (x, Op.ADD, y) ->
     Exp.BINOP (linear_exp ~in_terms:constants x, Op.ADD, linear_exp ~in_terms:constants y)
  | Exp.BINOP (x, Op.SUB, y) ->
     Exp.BINOP (linear_exp ~in_terms:constants x, Op.SUB, linear_exp ~in_terms:constants y)
  | Exp.BINOP (x, Op.MUL, Exp.CONST c)
    | Exp.BINOP (Exp.CONST c, Op.MUL, x) ->
     Exp.BINOP (Exp.CONST c, Op.MUL,  linear_exp ~in_terms:constants x)
  | Exp.BINOP (x, Op.MUL, y) ->
     if x |<- constants then
       Exp.BINOP (x, Op.MUL, linear_exp ~in_terms:constants y)
     else if y |<- constants then
       Exp.BINOP (linear_exp ~in_terms:constants x, Op.MUL, y)
     else
       Term.toExp (VcpVBase.qvar ())
  | Exp.FCALL (s,ts) -> Exp.FCALL (s, ts)
  | _ -> Term.toExp (VcpVBase.qvar ())

let linear_term = function
    Term.NULL -> Term.NULL
  | Term.EXP e -> Term.EXP (linear_exp e)

let to_linear t = linear_term $$ VcpVBase.peano_to_pb t

let rec to_linear_b = function
    BExp.UNIT (x, op, y) ->
     let x' = linear_term x in
     let y' = linear_term y in
     BExp.unit x' op y'
  | BExp.OP (x, op, y) ->
     let x' = to_linear_b x in
     let y' = to_linear_b y in
     BExp.op x' op y'
  | x -> x

let rec is_exact b =
  contains_no_undef_in_bexp b

let rec is_while_exact b =
  contains_no_undef_in_bexp b &&
    match b with
      BExp.UNIT (x, _, y) -> is_term_linear x && is_term_linear y
    | BExp.OP   (_, Op.OR, _) -> false
    | BExp.OP   (x, _, y) -> is_while_exact x && is_while_exact y
    | _ -> true (** @Jul29 *)

let conj_d_A bs _A =
  (fun (a,b,c,d) -> (a,b @ bs,c,d)) _A

let conj store bexps formula =
  let (ex, pures, pointers, preds) = formula in
  let _store = M.fold (fun key value acc ->
                   if value = Term.EXP Exp.UNDEF then acc else (** @Jul29 *)
                     (BExp.UNIT (Term.EXP key, Op.EQ, value)) :: acc) store [] in
  let pures' = BExp.(pures &&~ _store &&~ bexps) in
  (ex, pures', pointers, preds)

let _C c   = Exp.CONST c
let (@+) a b = Exp.op a b Op.ADD
let (@-) a b = Exp.op a b Op.SUB
let (@*) a b = Exp.op a b Op.MUL

let _True  = BExp._T
let _False = BExp._F
let _Inf   = Exp.POSINF
let _NInf  = Exp.NEGINF

let (<.) a b = BExp.(a <. b)
let (==) a b = BExp.(a == b)
let (=/) a b = BExp.(a =/ b)
let (@<) a b = (_T a) <. (_T b)
let (@=) a b = (_T a) == (_T b)

let (|.) a b   = BExp.(a |. b)
let (&.) a b  = BExp.(a &. b)
let (@+@) a b = Term.op a b Op.ADD
let (@-@) a b = Term.op a b Op.SUB
let (@*@) a b = Term.op a b Op.MUL
let (@<=) a b = ((a <. b) |. (a == b))

let (-->) a b = VcpVBase.entail "LIST2" ([],a,[],[]) ([],[b],[],[])
let ( *** ) = Formula.( *** )


let is_valid_array (_, data) =
  match data with
    l::u::_ ->
     VcpVBase.check_sat2 ([], [l @<= u],[],[])
  | _ -> false

let joinformula (f:Formula.ut) (ca,cb,cc,cd) =
  let f1 = Formula._Exs f ca in
  let f2 = Formula.(f1 &~~ cb) in
  let f3 = Formula.(f2 *~~ cc) in
  let f4 = Formula.(f3 #~~ cd) in
  f4

let fuse_missing _B (a, b, c, d, e, f) = (a, b, c, joinformula _B d, e, f)

let _Addr (_, _, ptrs, preds) =
  let pts = (fun (p,_)->(p,p)) |>>| ptrs in
  let prs = (fun (_,data)-> (List.hd data, List.hd $$ List.tl data)) |>>| ((fun (pn,_) -> pn = "Array") |>- preds) in
  pts @ prs

let not_in_Addr (t:Term.t) (_,_,ptrs,preds) =
  let hs = (function Term.EXP (Exp.ADDR (_)) -> false | _ -> true) |>- (fst |>>| ptrs) in
  if List.exists (fun h -> h=t) hs then
    [BExp._F]
  else
    let arrays = (fun acc (s, data) ->
        if s = "Array" then
          match data with
            l::u::_ -> (l,u)::acc
          | _ -> acc
        else
          acc
      ) |->> ([], preds) in
    let lists : BExp.t list = (fun acc (s, data) ->
        if s = "List" then
          match data with
            t'::u::_ -> ((t =/t')|. (t'==u))::acc (** Points to discuss *)
          | _ -> acc
        else
          acc
      ) |->> ([], preds) in


    let hs'  = (fun h -> (t =/ h)) |>>| hs in
    let arrays' = (fun (l,u) -> (t <. l) |. (u <. t)) |>>| arrays in
    
    let res = hs' @ arrays' @ lists in
    res

let rec e_eval ?alt_s:(alt=M.empty) _s _L exp =
  let op o t1 t2 =
       match t1, t2 with
         Term.EXP e1, Term.EXP e2 ->
          let e = Exp.BINOP (e1, o, e2) in
          let e' = Exp.eval e in
          _T e'
       | _, _ -> Term.NULL
  in
  match exp with
  | Exp.UNDEF -> _T Exp.UNDEF
  | Exp.NOTHING -> _T Exp.NOTHING
  | (Exp.VAR v) as ev ->
     begin
       let v' =
         let sv = Exp.var_to_str v in
         if sv |<- !all_functions then
           if F.mem sv !f_heap then
             F.find sv !f_heap
           else
             add_f sv
         (* else if Exp.is_question v then
            Term.encode v *)
         else if M.mem ev _s then
           M.find ev _s
         else if M.mem ev alt then
           M.find ev alt
         else
           let v' =
             if Exp.is_check ev || Exp.is_hat ev || Exp.is_tilde ev || Exp.is_bar ev || Exp.is_dot ev then
               ev
             else
               Exp.set_bar ev
           in
           Term.EXP v'
       in
       v'
     end
  | Exp.FCALL (s,ts) -> _T (Exp.FCALL (s, Term.toExp |>>| (e_eval ~alt_s:alt _s _L |>>| ts)))
  | Exp.BINOP (x, o, y) ->
     begin
       let x' = e_eval ~alt_s:alt _s _L x in
       let y' = e_eval ~alt_s:alt _s _L y in
       op o x' y'
     (*
       match o with  (** @Jul29 *)
       | Op.MUL ->
       begin
       match x', y' with
       Term.EXP (Exp.CONST _), _
       | _, Term.EXP (Exp.CONST _) -> op o x' y'
       | _, _ -> op o x' y' (* Term.EXP Exp.UNDEF *)
       end
       | Op.DIV | Op.MOD ->
       begin
       match x', y' with
       | _, Term.EXP (Exp.CONST _) -> op o x' y'
       | _, _ -> op o x' y' (* Term.EXP Exp.UNDEF *)
       end
       | Op.SHR ->
       begin
       match x', y' with
       | _, Term.EXP (Exp.CONST cy) ->
       let py = Exp.power_2 cy in
       op Op.DIV x' (Term.EXP (Exp.CONST py))
       | _, _ -> op Op.SHR x' y' (* Term.EXP Exp.UNDEF *)
       end
       | Op.SHL ->
       begin
       match x', y' with
       | _, Term.EXP (Exp.CONST cy) ->
       let py = Exp.power_2 cy in
       op Op.MUL x' (Term.EXP (Exp.CONST py))
       | _, _ -> op Op.SHL x' y' (* Term.EXP Exp.UNDEF *)
       end
       | Op.ADD | Op.SUB ->
       op o x' y'
       | _ -> op o x' y' (** Supporting Peano Term *)
      *)
     end
  | Exp.REF (e) ->
     (* Term.encode (new_prog_var (), [Exp.QUESTION]) *)
     Term.EXP Exp.UNDEF
  | Exp.LBL (lbl, e) ->
     begin
       try
         let _s' = F.find lbl _L in
         e_eval ~alt_s:alt _s' _L e
       with
         _ -> e_eval _s _L e (* raise (StError ("L is undefined in eval ()@" ^ lbl)) *)
     end
  | Exp.INDICES e ->
     let e' = (e_eval ~alt_s:alt _s _L) |>>| e in
     begin
       match e' with
         [] -> Term.EXP (Exp.CONST 0)
       | x::xs -> ((fun a b -> op Op.MUL a b) |->> (x, xs))
     end
  | Exp.ADDR ((Exp.VAR vv) as e) ->
     let se = fst vv in
     if se |<- !all_functions then
       e_eval ~alt_s:alt _s _L e
     else
       e_eval ~alt_s:alt _s _L e (** Temporary Implementation *)
  | Exp.ADDR e ->
     _T (Exp.ADDR e)
  (* | Exp.SIZEOF (_tau) ->
     _T (_C (Exp._struct_size_by_name !all_struct _tau)) *)
  | c -> _T c

let rec eval ?alt_s:(alt=M.empty) _s _L e =
  match e with
    Term.NULL -> Term.NULL
  | Term.EXP e ->
     let e' = e_eval ~alt_s:alt _s _L e in
     e'


let rec eval_b ?alt_s:(alt=M.empty) (_L : Term.t M.t F.t) (_s : Term.t M.t) = function
    BExp.UNIT (t1, o, t2) ->
     let t1' = eval ~alt_s:alt _s _L t1 in
     let t2' = eval ~alt_s:alt _s _L t2 in
     let res = BExp.unit t1' o t2'  (** @Jul29 *) in
     res
  | BExp.OP (b1, o, b2) ->
     let b1' = eval_b ~alt_s:alt _L _s b1 in
     let b2' = eval_b ~alt_s:alt _L _s b2 in
     BExp.op b1' o b2'     (** @Jul29 *)
  | BExp.LBL (lbl, b) ->
     begin
       try
         let _s' = F.find lbl _L in
         if M.cardinal alt = 0 then
           eval_b ~alt_s:_s _L _s' b
         else
           eval_b ~alt_s:_s _L alt b
       with
         _ ->
         (* p "LABEL "; p lbl; pn " NOT Found"; *)
         BExp._T
     end
  | _ -> raise Error (* BExp.NOTHING *)

let eval_pointer _s _L (p, fields) =
  let p' = eval _s _L p in
  (p', (fun (f, v) -> f, eval _s _L v) |>>| fields)

let eval_formula _s _L (a,b,c,d) =
  let b' = (eval_b _L _s) |>>| b in
  let c' = (eval_pointer _s _L) |>>| c in
  let d' = (fun (nm,dt) -> (nm, ((eval _s _L) |>>| dt))) |>>| d in
  (a, b', c', d')

let subs x v s =
  let s' = if M.mem x s then M.remove x s else s in
  let s'' = M.add x v s' in
  s''

let is_bexp_sat bexps =
  VcpVBase.check_sat2 ([],bexps,[],[])
  
(** pure(A) *)
let _pure ((_, pures, ptrs', preds') : Formula.ut) =
  let pointer_locs : Term.t list = (function Term.EXP (Exp.ADDR (_)) -> false | _ -> true) |>- (fst |>>| ptrs') in
  let preds = Predicate.filter "Array" preds' in
  let lists' = Predicate.filter "List" preds' in
  let lists = (function (_, a::b::_) -> is_bexp_sat [(a == b)] | _ -> false) |>- lists' in
  let bounds = (fun data -> (List.hd data, List.hd (List.tl data))) |>>| (snd |>>| preds) in
  let _in_cross ls = (** ls is an arbitrary list. It will produce cross of ls and ls *)
    let res, _ = (fun (acc, ls) p ->
        let tl = List.tl ls in
        (acc @ ((fun l -> (p,l)) |>>| tl), tl)
      ) |->> (([], ls), ls) in
    res
  in
  let ps_bexp = (fun (p,l) -> BExp.(p =/ l)) |>>| (_in_cross pointer_locs) in
  let _not_in p (a, b) = (p <. a) |. (b <. p) in
  let _no_intersect (aj,bj) (ak,bk) = (bj <. ak) |. (bk <. aj) in
  let pt_pr_bexp = concat ((fun p -> (_not_in p) |>>| bounds) |>>| pointer_locs) in
  let pr_bexp = (fun (j,k) -> _no_intersect j k) |>>| (_in_cross bounds) in
  let ls_pointers = concat ((fun ti -> (function (_, cl::_) -> ti =/ cl | _ -> raise Error) |>>| lists) |>>| pointer_locs) in
  let ls_arrays = concat ((fun (aj,bj) -> (function (_, cl::_) -> (cl <. aj) |. (bj <. cl) | _ -> raise Error) |>>| lists) |>>| bounds) in
  let ls_lists = (function ((_, a::_), (_, b::_)) -> a == b | _ -> _False) |>>| _in_cross lists in
  BExp.(pures &&~ ps_bexp &&~ pt_pr_bexp &&~ pr_bexp &&~ ls_pointers &&~ ls_arrays &&~ ls_lists)

let sat_A _A = (fun (_,d,a,_,_,_) -> is_bexp_sat $$ _pure (Formula.(a &~~ d))) |>- _A
             
let extract_list _L _s _d _A t is_list_head =
  let t = Term.eval t in
  if Term.with_head t then
    let thd = Term.head (Term.toStr t) t in
    if Exp.is_struct thd then
      let typ = Exp.get_struct_name thd in
      let s_t = eval _s _L t in
      begin
        dbg "EXLIST" "Given A:" Formula.pprint [_A];
        let (_, _, ptrs, preds) = _A in
        let rec get_lists res prefix = function
            [] -> res
          | (("List", contents) as pr)::suffix ->
             begin
               match contents with
                 t'::u::_ ->
                  if Term.with_head t' then
                    let t'hd = Term.head "" t' in
                    if not (Exp.is_struct t'hd) || Exp.get_struct_name t'hd = typ then
                      begin
                        (** Same Type *)
                        let y_tld = _T $$ newvar [] in
                        let ls1 = ("List", [y_tld;u]) in
                        let to_check, _d' =
                          if is_list_head then
                            let d1 = [t' == s_t; t' =/ u] in (**  *)
                            let _d' = BExp.(_d &&~ d1) in
                            _d', _d'
                          else
                            let cell1 = (s_t, []) in
                            let d1 = _pure ([], [], cell1::ptrs, ls1::prefix@suffix) in
                            let d2 = [t' =/ s_t; t' =/ u; s_t =/ u] in
                            BExp.(_d &&~ d1), d2
                        in
                        dbg "EXLIST" "To Check:" (iterS BExp.pprint "&") to_check;
                        if is_bexp_sat to_check then
                          begin
                            pn_s "EXLIST" "VALID";
                            (* let _s' = subs _x x_tld _s in
                            let _d'  = to_check in
                            let _A' =   _PutVarAddr ([],[],(s_t, [("next",x_tld)])::ptrs, ("List", [x_tld;u])::prefix@suffix) _x x_tld in
                            let r = (_s',_d',_A',empty,[],_L) in *)
                            let r = (s_t, _d', (t', u, y_tld), ([],[],ptrs,prefix@suffix)) in
                            get_lists (r::res) (pr::prefix) suffix
                          end
                        else
                          begin
                            pn_s "EXLIST" "INVALID";
                            get_lists res (pr::prefix) suffix
                          end
                      end
                    else
                      get_lists res (pr::prefix) suffix
                  else
                    get_lists res (pr::prefix) suffix
               | _ -> get_lists res (pr::prefix) suffix
             end
          | pr::suffix -> get_lists res (pr::prefix) suffix
        in

        get_lists [] [] preds
      end
    else
      []
  else
    []


(** A = A' * Arr(t', t'')
    s and d and A |= t' <= t <= t''
    A is transformed into A' * Arr(t', t-1) * t -> z^ * Arr(t+1,t'') *)
let get_array_bound (_L : (Term.t M.t) F.t) _pr _s _d _A (t : Term.t) =
  (** Assumption: t does not have the form *(_) *)
  let t = Term.eval t in
  let s_t = eval _s _L t in
  begin
    dbg "ARRAY" ("Checking " ^ _pr ^ " Bound for") Term.pprint t;
    dbg "ARRAY" "Given A:" Formula.pprint [_A];
    let (_, _, ptrs, preds) = _A in
    let left _t' _ = _t' @<= s_t in (* BExp.OP (BExp.UNIT(_t', Op.LE, t), Op.OR, BExp.UNIT(_t', Op.EQ, t)) in *) (** t' <= t *)
    let right _ _t'' = s_t @<= _t'' in (*  BExp.UNIT(t, Op.LE, _t'') in*) (** t <= t'' *)
    let bs _t' _t''= [left _t' _t''; right _t' _t''] in
    let con _t' _t'' = (eval_formula _s _L) |>>| [([],bs _t' _t'', [], [])] in (** s(t' <= t & t < t'') *)
    (* let leftF = [conj M.empty _d _A] in *)
    let sthd, sthd_fs =
      if Term.with_head s_t then
        Term.head (Term.toStr t) s_t, false
      else if Term.is_fp s_t && Term.with_head t then
        Term.head "" t, false
      else
        __E ("",[]), Term.is_fp s_t in
    let thd = Term.head (Term.toStr t) t in
    try
      begin
        let matched =
          (fun (nm, contents) ->
            if nm = _pr then
              match contents with
                (Term.EXP e_arr)::t_last::_ ->
                 let t'hd, t'hd_fs =
                   if Term.with_head (Term.EXP e_arr) then
                     Exp.head (Exp.toStr e_arr) e_arr, false
                   else
                     __E ("",[]), Exp.is_fp e_arr
                 in
                 let to_compare =
                   if sthd_fs || t'hd_fs then
                     true
                   else
                     ((fst (__V t'hd) = fst (__V sthd)) || (Exp.is_not_local t'hd && Exp.is_not_local thd)) (* && is_same_type *)
                 in
                 if to_compare then
                   begin
                     pn_s "ARRAY" "to_compare=true";
                     let rightF : Formula.t = con (Term.EXP e_arr) t_last in
                     dbg "ARRAY" "rightF:" Formula.pprint rightF;
                     let to_check' = (fun (a',b',c',d') -> (fun (a,b,c,d) -> (a@a',b@_d@b',c@c',d@d')) _A) |>>| rightF in
                     let to_check = (fun a -> ([],_pure a,[],[])) |>>| to_check' in
                     (* pf_s "ARRAY" Formula.pprint leftF; p_s "ARRAY" "|- "; pf_s "ARRAY" Formula.pprint rightF; pn_s "ARRAY" ""; *)
                     dbg "ARRAY" "d & A & s(t' <= t <= t'') for sat checking:" Formula.pprint to_check;
                     let res = List.for_all VcpVBase.check_sat2 to_check in
                     (* let res = (VcpVBase.entail_all "ARRAY" leftF [rightF]) in *)
                     if res then pn_s "ARRAY" "VALID" else pn_s "ARRAY" "INVALID";
                     res (** (ConvFtoK.decide_semientl_b [(leftF, rightF)]) *)
                   end
                 else
                   begin
                     pn_s "ARRAY" "to_compare=false";
                     false
                   end
              | _ -> false
            else
              false
          ) |>- preds in

        match s_t with
          Term.EXP t ->
           dbg "ARRAY" (_pr ^ " matches:") pl (List.length matched);
           (fun ((_, data) as p) ->
             match data with
               _t'::_t''::_ ->
                let first1 = eval _s _L _t' in
                let last2  = eval _s _L _t'' in
                let last1  = eval _s _L (Term.EXP (t @- (_C 1))) in
                let first2 = eval _s _L (Term.EXP (t @+ (_C 1))) in
                let bs' = bs first1 last2 in
                let unmatched_pred = (fun p' -> not (p=p')) |>- preds in
                (first1, last1, first2, last2, bs', unmatched_pred)
             | _ -> raise (StError "Exception: Unexpected Array Shape")
           ) |>>| matched
        | _ -> raise (StError "Exception: NULL Pointer Dereferenced")
      end
    with
    | _ -> []
  end

let get_ptr _L _s _d _A t =
  (** Assumption: t does not have the form *(_) *)
  let t = Term.eval t in
  let s_t = eval _s _L t in
  let sthd, sthd_fs =
    if Term.with_head s_t then
      Term.head (Term.toStr t) s_t, false
    else
      __E ("",[]), Term.is_fp s_t
  in
  let (_, _, ptrs, preds) = _A in
  print_pre "GET_PTR" _s _d _A (Locs.dummy);
  dbg "GET_PTR" "To Search(t):" Term.pprint t;
  dbg "GET_PTR" "To Search(s(t)):" Term.pprint s_t;
  let matched =
    (fun (t',_) ->
      dbg "GET_PTR" "Case:" Term.pprint t';
      begin
        let t'hd, t'hd_fs =
          if Term.with_head t' then
            Term.head (Term.toStr t') t', false
          else
            __E ("",[]), Term.is_fp t'
        in
        let to_compare =
          if sthd_fs || t'hd_fs then
            true
          else if not (Exp.is_struct t'hd = Exp.is_struct sthd) then
            false
          else if not (Exp.is_ptrptr t'hd = Exp.is_ptrptr sthd) then
            false
          else if Exp.is_struct t'hd && Exp.is_struct sthd then
            Exp.get_struct_name t'hd = Exp.get_struct_name sthd
          else
            (__N t'hd = __N sthd) || (Exp.is_not_local t'hd && Exp.is_not_local sthd)
        in
        
        if to_compare then
          begin
            let rightF = BExp.(s_t == t') in
            let non_pure = (fun (a,b,c,d) -> (a,b@_d@[rightF],c,d)) _A in
            let to_check = ([], _pure non_pure, [], []) in (** @Aug7 *)
            dbg "GET_PTR" "s(t)=t':" BExp.pprint rightF;
            let res =
              try
                VcpVBase.check_sat2 to_check
              with
                e ->
                pn "";
                Formula.upprint non_pure;
                pn "";
                raise e
            in
            if res then pn_s "GET_PTR" "VALID" else pn_s "GET_PTR" "INVALID";
            res
          end
        else
          begin
            dbg "GET_PTR" "No compare: " Exp.pprint t'hd;
            false
          end
      end
    ) |>- ptrs in
  (fun p ->
    let unmatched = (fun p' -> not (p=p')) |>- ptrs in
    (p, unmatched)
  ) |>>| matched

(** ******************
    NORMALIZATION
    ****************** *)
  
let rec contract_ptr_ptr f p ffv (_A : 'a list) (xs : 'b list) (old : 'b list) : ('b list * 'a list) =
  match xs with
    [] -> (old, _A)
  | x::xs ->
     dbg "LIST2" "The Pred/Ptr:" p x;
     dbg "LIST2" "Latest Pointers:" (iterS p "*") xs;
     dbg "LIST2" "Latest Predicates:" (iterS Predicate.pprint "*") _A;
     let r = f x xs _A ffv old in
     match r with
       None ->
        pn_s "LIST2" "No Contract";
        let (r',_A') = contract_ptr_ptr f p ffv _A xs (x::old) in
        (r', _A') (** x::r'*)
     | Some (r',_A') ->
        pn_s "LIST2" "Contracted";
        dbg "LIST2" "Contracted in:" (iterS p "*") r';
        dbg "LIST2" "Contracted in:" (iterS Predicate.pprint "*") _A';
        
        contract_ptr_ptr f p ffv _A' r' []

        
let rec contract f p ffv (_A : 'a list) (xs : 'b list) (old : 'b list) : ('b list * 'a list) =
  match xs with
    [] -> (old, _A)
  | x::xs ->
     dbg "LIST2" "The Pred/Ptr:" p x;
     dbg "LIST2" "Latest Pointers:" (iterS p "*") xs;
     dbg "LIST2" "Latest Predicates:" (iterS Predicate.pprint "*") _A;
     let r = f x xs _A ffv old in
     match r with
       None ->
        pn_s "LIST2" "No Contract";
        let (r',_A') = contract f p ffv _A xs (x::old) in
        (r', _A') (** x::r'*)
     | Some (r',_A') ->
        pn_s "LIST2" "Contracted";
        dbg "LIST2" "Contracted in:" (iterS p "*") r';
        dbg "LIST2" "Contracted in:" (iterS Predicate.pprint "*") _A';
        
        contract f p ffv _A' r' []

let normalize (_s', _d, _A) =
  let (_, _, ptrs00, preds0) = _A in
  dbg "LIST2" "Before Indirect Analysis:" (iterS Pointer.pprint "*") ptrs00;

  let s_fvs = M.fold (fun _ v fvs -> fvs @@ Term.fv v) _s' [] in
  dbg "LIST2" "FV(Range(s)):" (iterS Exp.pprint ", ") s_fvs;
  let rec ptr_process saved cells = function
      [] -> saved, cells
    | ((ptr, fields0) as cell)::xs ->
       if Exp.is_indirect $$ Term.toExp ptr then
         ptr_process saved cells xs
       else
         (
           let fields', saved', cells =
             (fun (fields, saved, cells) (fn, dt) ->
               let dt_v = Term.toExp dt in
               if not (dt_v |<- s_fvs) && Exp.is_indirect dt_v then
                 (
                   let cells' = (fun pp -> not (pp = cell)) |>- cells in
                   let selected, rest = List.partition (fun (pt',_) ->
                                            pt'= dt
                                          ) cells' in
                   
                   if List.length selected = 0 then
                     (
                       Pointer.pprint (ptr,fields0); 
                       raise (StError "no indirect found"))
                   else
                     let (_, fields') = try List.hd selected with e ->
                                          raise e  in
                     (** We assume that indirect cells are always in x->("*":t) pattern *)
                     let (_, in_dt) = List.hd fields' in
                     let fields' = fields @ [(fn, in_dt)] in
                     let saved' = saved @ [((ptr, fn), dt)] in
                     (fields', saved', rest)
                 )
               else
                 (fields@[(fn, dt)], saved, cells)
             ) |->> (([], [], cells), fields0)
           in
           if List.length saved' > 0 then
             ptr_process (saved@saved') (cells @ [(ptr, fields')]) xs
           else
             ptr_process saved cells xs
         )
  in

  let (saved, ptrs0) = ptr_process [] ptrs00 ptrs00 in

  dbg "LIST2" "After Indirect Analysis:" (iterS Pointer.pprint "*") ptrs0;
  dbg "LIST2" "saved data:" (iterS (fun ((a,b),c) -> Term.pprint a; p "."; pw b; p":"; Term.pprint c) ",") saved;
  
  (** Common Law *)
  let subtract (a, b, ptrs, preds) ((_, _, ptrs0, preds0):Formula.ut) =
    let ptrs' = (fun a b -> if b |<- ptrs0 then a else b::a) |->> ([], ptrs) in
    let preds' = (fun a b -> if b |<- preds0 then a else b::a) |->> ([], preds) in
    ([], [], ptrs', preds')
  in
  
  let is_in_Addr _u ((_, _, ptrs, preds) as _A) =
    dbg "LIST2" "A:" Formula.upprint _A;
    let r1 = List.exists (fun ((a,b) : Predicate.t) ->
                 match a, b with
                   "List", b'::_ ->
                    (_d --> (b' == _u))
                 | "Stringpart", b'::c'::_
                   | "Array", b'::c'::_ ->
                    (_d --> (b' == _u)) && (_d --> (c' == _u))
                 | _ -> false
               ) preds in
    let r2 = List.exists (fun (pt, _) ->
                 _d --> (pt == _u)) ptrs in
    r1 || r2
  in
  
  let is_cond_met _A _u _tv ffv old =
    match _tv with
      Term.EXP (Exp.VAR _v) ->
       dbg "LIST2" "v:"  Exp.var_pprint _v;
       let _u_is_NULL = _u == Term.NULL in
       dbg "LIST2" "u==NULL:" BExp.pprint _u_is_NULL;
       let r1 = _d --> _u_is_NULL in
       dbg "LIST2" "u=NULL:" pb r1;
       let r2 = is_in_Addr _u _A in
       dbg "LIST2" "u in Addr(A'):" pb r2;
       let fv_range_s = (M.fold (fun _ v fv -> fv @@ Term.fv v) _s' []) in
       dbg "LIST2" "s:" (m_print "LIST2") _s';
       dbg "LIST2" "FV(Range(s)):" (iterS Exp.pprint ",") fv_range_s;
       dbg "LIST2" "v:" Exp.var_pprint _v;
       let r3 = not (__E _v |<- fv_range_s) in
       dbg "LIST2" "v notin Rangs(s):" pb r3;
       let fv_A = Formula.fv _A @ List.concat (ffv |>>| old) in
       dbg "LIST2" "A':" Formula.upprint _A;
       dbg "LIST2" "FV(A'):" (iterS Exp.pprint ",") fv_A;
       let r4 = not (__E _v |<- fv_A) in
       dbg "LIST2" "v notin FV(A'):" pb r4;
       let r = (r1 || r2) && r3 && r4 in
       dbg "LIST2" "Finally:" (fun r -> if r then p "True" else p "False") r;
       r
    | _ -> false
  in
  
  (* First Law *)
  let is_a_ptr_ptr_contraction ((_, data1) as x) ((_v2, data2) as x') _A ffv old =
    try
      dbg "LIST2" "x:" Pointer.pprint x;
      dbg "LIST2" "x':" Pointer.pprint x';
      let (_, _v1) = List.find (fun (fn, _) -> fn = "next" ) data1 in
      let (_, _u) = List.find (fun (fn, _) -> fn = "next" ) data2 in
      _d --> (_v1 == _v2) && is_cond_met (subtract _A ([],[],[x;x'],[])) _u _v1 ffv old
    with
      _ -> false
  in
  
  let make_new_list_from_ptr (_t : Term.t) (data : (bytes * Term.t) list) =
    try
      let (_, _v) = List.find (fun (f, _) -> f = "next") data in
      ("List", [_t;_v])
    with
      e ->
      pn "Error at make_new_list_from_ptr";
      raise e
  in
  
  let norm_ptr_ptr (x : Pointer.t) (ptrs : Pointer.t list) (preds : Predicate.t list) ffv old: (Pointer.t list * Predicate.t list) option =
    let _A = ([], [], ptrs0, preds) in
    match x with
      (_t, data) when "next" |<- (fst |>>| data) ->
       begin
         let matched, unmatched = List.partition (fun x' -> is_a_ptr_ptr_contraction x x' _A ffv old) ptrs in
         match matched with
           (_v, data')::rest ->
            Some (rest @ unmatched @ old, make_new_list_from_ptr _t data'::preds)
         | _ ->
            begin
              let matched, unmatched = List.partition (fun x' -> is_a_ptr_ptr_contraction x' x _A ffv old) ptrs in
              match matched with
                (_v, data')::rest ->
                 Some (rest @ unmatched @ old, make_new_list_from_ptr _v data::preds)
              | _ ->
                 None
            end
       end
    | _ -> None
  in
  
  let (ptrs1, preds1) = contract_ptr_ptr norm_ptr_ptr Pointer.pprint Pointer.fvs preds0 ptrs0 [] in
  dbg "LIST2" "After ptr-ptr:" (iterS Pointer.pprint "*") ptrs1;
  pn_s "LIST2" "";
  
  let make_new_list st en =
    let new_list = ("List", [st;en]) in
    dbg "LIST2" "New List:" Predicate.pprint new_list;
    new_list
  in
  
  (** Second Law *)
  let is_a_ptr_ls_contraction x _A ffv old x' =
    match x, x' with
      (_, data), ("List", _v::_u::_) when "next" |<- (fst |>>| data) ->
       dbg "LIST2" "x:" Pointer.pprint x;
       dbg "LIST2" "x':" Predicate.pprint x';
       let _, _v' = List.find (fun (fn, _) -> fn = "next") data in
       _d --> (_v == _v') && is_cond_met (subtract _A ([],[],[x],[x'])) _u _v ffv old
    | _ -> false
  in
  
  (** Third Law *)
  let is_a_ls_ptr_contraction x _A ffv old x' =
    match x', x with
      ("List", _::_v::_), (_v', data) when "next" |<- (fst |>>| data) ->
       dbg "LIST2" "x:" Pointer.pprint x;
       dbg "LIST2" "x':" Predicate.pprint x';
       let _, _u =
         try
           List.find (fun (fn, _) -> fn = "next") data
         with
           e ->
           pn "Error at is_a_ls_ptr_contraction";
           raise e
       in
       _d --> (_v == _v')  && is_cond_met (subtract _A ([],[],[x],[x'])) _u _v ffv old
    | ("List", hd::(Term.EXP ((Exp.VAR _) as v) as tl)::_), (pt, ("*",dt)::_) when Exp.is_indirect v ->
       _d --> (tl == pt) && is_cond_met (subtract _A ([],[],[x],[x'])) dt tl ffv old
    | _ -> false
  in

  let rec norm_ptr_ls (x : Pointer.t) (ptrs : Pointer.t list) (preds : Predicate.t list) ffv old : (Pointer.t list * Predicate.t list) option =
    let _A = ([], [], old@ptrs, preds) in
    match x with
      (_t, data) when "next" |<- (fst |>>| data) ->
       begin
         let matched, unmatched = List.partition (is_a_ptr_ls_contraction x _A ffv old) preds in
         match matched with
           ("List", _v::_u::_)::rest ->
            pn_s "LIST2" "PTR-LS Contract";
            Some (ptrs@old, make_new_list _t _u::unmatched@rest)
         | _ ->
            begin
              let matched, unmatched = List.partition (is_a_ls_ptr_contraction x _A ffv old) preds in 
              match matched with
                ("List", _t::_::_)::rest ->
                 begin
                   pn_s "LIST2" "LS-PTR Contract";
                   let _, _u =
                     try
                       List.find (fun (fn, _) -> fn = "next") data
                     with
                       e ->
                       pn "Error at norm_ptr_ls";
                       raise e
                   in
                   Some (ptrs@old, make_new_list _t _u::unmatched@rest)
                 end
              | _ ->
                 None
            end
       end
    | (Term.EXP ((Exp.VAR _) as v), data) when Exp.is_indirect v ->
       begin
         let matched, unmatched = List.partition (is_a_ls_ptr_contraction x _A ffv old) preds in
         match matched with
           ("List", hd::tl::_)::rest ->
            let _, _u = List.hd data in
            Some (ptrs@old, make_new_list hd _u::unmatched@rest)
         | _ -> None
       end
    | _ -> None
  in
  
  let ptrs2, preds2 = contract norm_ptr_ls Pointer.pprint Pointer.fvs preds1 ptrs1 [] in

  (** Fourth Law *)
  let is_a_ls_ls_contraction x x' _A ffv old : bool =
    match x, x' with
      ("List", _t::_v::_), ("List", _v'::_u::_) ->
       begin
         dbg "LIST2" "List:" Predicate.pprint x;
         dbg "LIST2" "Against:" Predicate.pprint x';
         dbg "LIST2" "d:" (iterS BExp.pprint "&") _d;
         dbg "LIST2" "en == st'" BExp.pprint (_v == _v');
         _d --> (_v == _v') && is_cond_met (subtract _A ([],[],[],[x;x'])) _u _v ffv old
       end
    | _, _ -> false
  in
  
  let  norm_ls_ls (x : Predicate.t) (xs : Predicate.t list) (_preds : Predicate.t list) ffv old =
    let _A = ([],[],ptrs2,_preds) in
    match x with
      ("List", st::en::_) ->
       begin
         let matched, unmatched = List.partition (fun x' -> is_a_ls_ls_contraction x x' _A ffv old) xs in
         match matched with
           (_, _::en'::_)::rest ->
            let preds' = make_new_list st en'::rest @ unmatched in
            Some (preds'@old, preds')
         | _ ->
            begin
              let matched, unmatched = List.partition (fun x' -> is_a_ls_ls_contraction x' x _A ffv old) xs in
              match matched with
                (_, st'::_::_)::rest ->
                 let preds' = make_new_list st' en::rest @ unmatched in
                 Some (preds'@old, preds')
              | _ ->
                 None
            end
       end
    | _ -> None
  in
  
  let (_, preds3) = contract norm_ls_ls Predicate.pprint Predicate.fvs preds2 preds2 [] in

  let saved_ptr = (fun ((a,_),_) -> a) |>>| saved in

  let lu t f =
    try
      let x = List.assoc (t,f) saved in
      Some x
    with
      _ -> None
  in
  
  let rec reconstruct_indirect = function
      [] -> []
    | ((ptr, fields) as cell)::xs ->
       if ptr |<- saved_ptr then
         let fields', newcells = (fun (fields', newcells) (fn, dt) ->
             match lu ptr fn with
               None -> (fields' @ [(fn, dt)], newcells)
             | Some d ->
                (fields' @ [(fn, d)], newcells@[(d, [("*", dt)])])                
           ) |->> (([], []), fields) in
         let cell = (ptr, fields') in
         cell::newcells @ reconstruct_indirect xs
       else
         cell :: reconstruct_indirect xs
  in

  let ptrs2' = reconstruct_indirect ptrs2 in
  
  dbg "LIST2" "Before Reconstruction:" (iterS Pointer.pprint "*") ptrs2;
  dbg "LIST2" "After Reconstruction:" (iterS Pointer.pprint "*") ptrs2';
  
  let _A' = ([], [], ptrs2', preds3) in
  (_s', _d, _A')

(** ******************
    SIGMA Computation
    ****************** *)
  
let get_sigma (_s1, _d'', (_A1 : Formula.ut)) (_s2, _d', _A2) =

  let print_sigma sigma =
    (print_pairs Term.pprint "-->" Term.pprint ",") sigma
  in
  (*
  let fvs_s_A =
    Formula.fv _A1 @@
      Formula.fv _A2 @@
        M.fold (fun _ v acc -> acc @@ Term.fv v) _s1 [] @@
          M.fold (fun _ v acc -> acc @@ Term.fv v) _s2 []
  in
   *)
  let rec cond_fold f (base:'a list) = function
      [] -> Some base
    | x::xs ->
       match f x with
         None -> None
       | Some r ->
          let r' = base @@ r in
          cond_fold f r' xs 
  in

  let rec cond_fold_rev f = function
      [] -> None
    | x::xs ->
       match f x with
         None ->
          cond_fold_rev f xs 
       | r -> r
  in

  let rec get_sigma_in_exp e1 e2 sigma =
    match e1, e2 with
      Exp.CONST c1, Exp.CONST c2 -> if c1=c2 then Some [] else None
    | Exp.VAR v1, _ ->
       if e1 = e2 then
         Some [(_TT v1, _T e1)]
       else
         begin
           match sigma with
             None -> None
           | Some sigs ->
              begin
                try
                  let (_,b) = List.find (fun (a,_) -> a=_TT v1) sigs in
                  if b = _T e2 then
                    Some [(_TT v1, _T e2)]
                  else
                    None
                with
                  Not_found ->
                  Some [(_TT v1, _T e2)]
              end
         end
    | Exp.BINOP (e11,o1,e12), Exp.BINOP (e21,o2,e22) ->
       begin
         let sig1 = get_sigma_in_exp e11 e21 sigma in
         let sig2 = get_sigma_in_exp e12 e22 (opcat sigma sig1) in
         match sig1, sig2 with
           Some g1, Some g2 -> Some (g1 @@ g2)
         | _, _ -> None
       end
    | _ -> None
  in
  let get_sigma_in_term t1 t2 sigma =
    match t1, t2 with
      Term.NULL, Term.NULL -> Some []
    | Term.EXP e1, Term.EXP e2 -> get_sigma_in_exp e1 e2 sigma
    | _, _ -> None
  in
  let sigma = M.fold (fun k v1 sigma ->
                  match sigma with
                    None -> None
                  | Some sig1 ->
                     try
                       let v2 = M.find k _s2 in
                       match get_sigma_in_term v1 v2 sigma with
                         None -> None
                       | Some sig2 -> Some (sig1@@sig2)
                     with
                       _ -> None
                ) _s1 (Some []) in
  let get_sigma_in_pointers (pt1, fields1) (pt2, fields2) sigma0 =
    
    match get_sigma_in_term pt1 pt2 sigma0 with
      None -> None
    | Some sigma ->
       if List.length fields1 = List.length fields2 then
         let fields_pairs = try
             List.combine fields1 fields2
           with
             _ ->
             Pointer.print_fields fields1;
             pn "";
             Pointer.print_fields fields2;
             raise (StError "Comb 1")
         in
         let f ((_, dt1), (_, dt2)) = get_sigma_in_term dt1 dt2 sigma0 in
         cond_fold f sigma fields_pairs
       else
         None
  in
  let get_sigma_in_predicates (pn1, data1) (pn2, data2) sigma0 =
    if pn1=pn2 && List.length data1 = List.length data2 then
      let data_pairs = try
          List.combine data1 data2
        with
          _ ->
          iterS Term.pprint "," data1;
          pn "";
          iterS Term.pprint "," data2; 
          raise (StError "Comb 2")
      in
      let f (dt1, dt2) = get_sigma_in_term dt1 dt2 sigma0 in
      cond_fold f [] data_pairs
    else
      None
  in
  match sigma with
    None ->
     None
  | Some sigs ->
     dbg "UNIFY" "Sigma from S:" print_sigma sigs;
     let rec is_sigma_consistent = function
         [] -> true
       | (x,t)::xs ->
          let r1 = List.for_all (fun (x',t') -> not (x=x') || t=t') xs in
          dbg "UNIFY" "No Mismatch:" pb r1;
          r1 && is_sigma_consistent xs
     in

     let rm x l = List.filter ((<>) x) l in
     let rec permutations = function  
       | [] -> []
       | x::[] -> [[x]]
       | l -> 
          List.fold_left (fun acc x -> acc @ List.map (fun p -> x::p) (permutations (rm x l))) [] l
     in 

     let eq_ptr ptrs1 ptrs2 sigma =
       let ptrs_pairs =
         try
           List.combine ptrs1 ptrs2
         with
           _ ->
           iterS (fun p -> Pointer.pprint p) ".," ptrs1;
           pn "";
           iterS (fun p -> Pointer.pprint p) ".," ptrs2;
           raise (StError "Comb:Pointer")
       in
       let f (ptr1, ptr2) = get_sigma_in_pointers ptr1 ptr2 (Some sigma) in
       match cond_fold f sigma ptrs_pairs with
         None -> None
       | (Some sigma' as r) ->
          dbg "UNIFY" "Temp Sigma(Ptr):" print_sigma sigma';
          if is_sigma_consistent sigma' then
            r
          else
            None
     in

     let eq_pred preds1 preds2 sigma =
       let pred_pairs = try
           List.combine preds1 preds2
         with
           _ ->
           iterS (fun p -> Predicate.pprint p) "," preds1;
           pn "";
           iterS (fun p -> Predicate.pprint p) "," preds2;
           raise (StError "Comb:Pred")
       in
       let f (pred1, pred2) = get_sigma_in_predicates pred1 pred2 (Some sigma) in
       match cond_fold f sigma pred_pairs with
         None -> None
       | (Some sigma' as r) ->
          dbg "UNIFY" "Temp Sigma(Pred):" print_sigma sigma';
          if is_sigma_consistent sigma' then
            r
          else
            None
     in
     
     let eq (_,_,ptrs1,preds1) (_,_,ptrs2,preds2) : bool * (Term.t * Term.t) list =

       if List.length ptrs1 <> List.length ptrs2 || List.length preds1 <> List.length preds2 then
         (false, [])
       else
         begin
           pn_s "UNIFY" "Original:";
           dbg "UNIFY" "\nptrs1:" (iterS Pointer.pprint " * ") ptrs1;
           dbg "UNIFY" "\nptrs2:" (iterS Pointer.pprint " * ") ptrs2;
           dbg "UNIFY" "\npreds1:" (iterS Predicate.pprint " * ") preds1;
           dbg "UNIFY" "\npreds2:" (iterS Predicate.pprint " * ") preds2;
           
           let unify (ptrs1 : Pointer.t list) (preds1 : Predicate.t list) : (Term.t * Term.t) list option =
             
             dbg "UNIFY" "ptrs1:" (iterS Pointer.pprint " * ") ptrs1;
             dbg "UNIFY" "ptrs2:" (iterS Pointer.pprint " * ") ptrs2;
             dbg "UNIFY" "preds1:" (iterS Predicate.pprint " * ") preds1;
             dbg "UNIFY" "preds2:" (iterS Predicate.pprint " * ") preds2;
             
             let r1 = eq_ptr ptrs1 ptrs2 sigs in
             match r1 with
               None ->
                pn_s "UNIFY" "No sigma from ptrs";
                None
             | Some sigma ->
                pn_s "UNIFY" "Some sigma from ptrs";
                let r2 = eq_pred preds1 preds2 sigma in
                match r2 with
                  None ->
                   pn_s "UNIFY" "No sigma from preds";
                   None
                | (Some _) as r2 ->
                   pn_s "UNIFY" "Some sigma from preds";
                   r2
           in

           let res = unify ptrs1 preds1 in
           match res with
             Some sigma -> (true, sigma)
           | None ->
              begin
                dbg "UNIFY" "\nPtrs1:" Formula.upprint ([],[],ptrs1,[]);
                dbg "UNIFY" "\n|Ptrs1|:" pl (List.length ptrs1);
                let perm_ptrs1 = permutations ptrs1 in
                dbg "UNIFY" "\n|Perm(Ptrs1)|:" pl (List.length perm_ptrs1);
                dbg "UNIFY" "\n|Preds1|:" pl (List.length preds1);
                let perm_preds1 = permutations preds1 in
                dbg "UNIFY" "\n|Perm(Preds1)|:" pl (List.length perm_preds1);

                dbg "UNIFY" "\nPtrs:" (iterS (fun x -> Formula.upprint ([],[],x,[]);) "\n") perm_ptrs1;
                pn_s "UNIFY" "-----------------";
                let res : (Term.t * Term.t) list option=
                  if List.length perm_ptrs1 > 0 && List.length perm_preds1 > 0 then
                    cond_fold_rev
                      (fun preds0 ->
                        cond_fold_rev
                          (fun ptrs0 ->
                            unify ptrs0 preds0
                          ) perm_ptrs1
                      ) perm_preds1
                  else
                    None
                in
                
                pn_s "UNIFY" "Unification is Done";
                
                match res with
                  None -> (false, [])
                | Some sigma -> (true, sigma)
              end
         end
     in
     
     dbg "UNIFY" "\nA1:" Formula.upprint _A1;
     dbg "UNIFY" "\nA2:" Formula.upprint _A2;
     let (r, sigs') = eq _A1 _A2 in
     dbg "UNIFY" "\nA1'=A2:" pb r;
     dbg "UNIFY" "\nsigmas:" (iterS (fun (a,b) -> Term.pprint a; p "-->"; Term.pprint b) ",") sigs'; 
     
     let _A1' = Formula.upar_subs sigs' _A1 in
     dbg "UNIFY" "\nA1':" Formula.upprint _A1';
     
     if r && is_sigma_consistent sigs' then
       begin
         pn_s "UNIFY" "Sigma is consistent";
         (* let fd' = ([], _d', [], []) in *)
         let smt_d' = bexp_to_smt_exp (BExp.list_to_bexp _d') in
         let _d''_subs = (fun d -> BExp.par_subs sigs' (BExp.eval d)) |>>| _d'' in
         let smt_d'' = bexp_to_smt_exp (BExp.list_to_bexp _d''_subs) in
         let smt_e = S.((S.not' smt_d') |^| smt_d'') in
         let fvs = E.fv smt_e in
         let smt_exp = S.all' fvs smt_e in
         
         (* let fd'' = ([], _d''_subs, [], []) in *)
         dbg "UNIFY" "d':" (iterS BExp.pprint "&") _d';
         dbg "UNIFY" "d'':" (iterS BExp.pprint "&") _d'';
         dbg "UNIFY" "(d'')sigma:" (iterS BExp.pprint "&") _d''_subs;

         (* let entail _d' _d''_subs =
           
           let rest = (fun d ->
               not (d |<- _d')
             ) |>- _d''_subs in
           dbg "LIST3" "to entail: True |- " (iterS BExp.pprint " & ") rest;
           let rest'' = (fun b -> List.exists (fun v -> v |<- fvs_s_A) (BExp.fv b)) |>- rest in
           List.length rest'' = 0
         in *)
         if Z.checkSatExpBool smt_exp (* VcpVBase.entail "SIGMA" fd' fd'' || entail _d' _d''_subs *) then
           (
             pn_s "UNIFY" "d' -> d''[sigma] is valid";
             Some sigs')
         else(
           pn_s "UNIFY" "d' -> d''[sigma] is not valid";
           None)

       end
     else(
       pn_s "UNIFY" "Sigma is not consistent";
       None
     )
;;

let rev_sig sigs = (fun (a,b) -> (b,a)) |>>| sigs
let get_rho sigs = (fun (a,b) -> (a, _T $$ newvar [])) |>>| sigs

let unify_contract pp unify _X _Y =
    let rec aux x = function
      [] -> None, []
    | y::ys ->
       match unify x y with
         None ->
          let (o, zs) = aux x ys in
          (o, y::zs)
       | Some z ->
          let (o, zs) = aux x ys in
          match o with
            Some o' -> Some (z::o'), zs
          | None -> Some [z], zs
  in
  let (ns,xs,ys) : 'o list * 'o list * 'o list =
    (fun ((ns,xs,ys):'o list * 'o list * 'o list) (x:'o) ->
      let (o, zs) : 'o list option * 'o list = aux x ys in
      match o with
        None -> ns, x::xs, zs
      | Some n -> n@ns, xs, zs
    ) |->> (([],[],_Y), _X) in
  ns @ xs @ ys;;
  
let _join _X' _Y' =
  (* _X' @ _Y'
   *)
  
  pn_s "JOIN" "--##--##--##--##--##--##--";
  dbg "JOIN" "X:\n" (iterS (fun x -> pprint_f "JOIN" x Locs.dummy) "\n") _X';
  dbg "JOIN" "Y:\n" (iterS (fun x -> pprint_f "JOIN" x Locs.dummy) "\n") _Y';
  
  let norm (s,d,a,b,q,r) =
    let (s',d',a') = normalize (s,d,a) in
    (s',d',a',b,q,r)
  in
  let _X = norm |>>| _X' in
  let _Y = norm |>>| _Y' in

  dbg "JOIN" "Norm(X):\n" (iterS (fun x -> pprint_f "JOIN" x Locs.dummy) "\n") _X;
  dbg "JOIN" "Norm(Y):\n" (iterS (fun x -> pprint_f "JOIN" x Locs.dummy) "\n") _Y;
  
  let whole_subs rho (s,d,a,b,q,r) : o =
    let s' = M.map (fun v -> Term.par_subs rho v) s in
    let d' = BExp.par_subs rho |>>| d in
    let a' = Formula.upar_subs rho a in
    let b' = Formula.upar_subs rho b in
    (s',d',a',b',q,r)
  in
  let unify ((s1,d1,a1,b1,q1,r1):o) ((s2,d2,a2,b2,q2,r2):o) =
    dbg "JOIN" "x:\n" (pprint_f "JOIN" (s1,d1,a1,b1,q1,r1)) Locs.dummy;
    dbg "JOIN" "y:\n" (pprint_f "JOIN" (s2,d2,a2,b2,q2,r2)) Locs.dummy;
    let o_sigma = try get_sigma (s1,d1,a1) (s2,d2,a2) with e -> pn "error at _join"; raise e in
    match o_sigma with
      None ->
       pn_s "JOIN" "No Sigma";
       None
    | Some sigs ->
       pn_s "JOIN" "Some Sigma";
       let d1' = BExp.list_to_bexp d1 in
       let d2' = BExp.list_to_bexp d2 in
       let sigs' = rev_sig sigs in
       let d2'' = BExp.par_subs sigs' d2' in
       let d = [(d1' |. d2'')] in
       let x' = (s1,d,a1,b1,q1,r1) in
       let rho = get_rho sigs in
       let x'' : o = whole_subs rho x' in
       Some x''
  in
  let res = unify_contract pprint_f unify _X _Y in
  dbg "JOIN" "X Unf Y:\n" (iterS (fun x -> pprint_f "JOIN" x Locs.dummy) "\n") res;

  if List.length _X' + List.length _Y' < List.length res then
    pn_s "JOIN" "\n@@ _join reduces\n";
  
  pn_s "JOIN" "--##--##--##--##--##--##--";
  res
;;


let _retjoin _X' _Y' =
  (* _X' @ _Y'
   *)
  let norm (r,s,d,a,b) =
    let (s',d',a') = normalize (s,d,a) in
    (r,s',d',a',b)
  in
  let _X = norm |>>| _X' in
  let _Y = norm |>>| _Y' in

  let whole_subs rho (r,s,d,a,b) : r =
    let r' = Term.par_subs rho r in
    let s' = M.map (fun v -> Term.par_subs rho v) s in
    let d' = BExp.par_subs rho |>>| d in
    let a' = Formula.upar_subs rho a in
    let b' = Formula.upar_subs rho b in
    (r',s',d',a',b')
  in
  let unify ((r1,s1,d1,a1,b1):r) ((r2,s2,d2,a2,b2):r) =
    let o_sigma = try get_sigma (s1,d1,a1) (s2,d2,a2) with e -> pn "Error at _retjoin"; raise e in
    match o_sigma with
      None -> None
    | Some sigs ->
       let d1' = BExp.list_to_bexp d1 in
       let d2' = BExp.list_to_bexp d2 in
       let sigs' = rev_sig sigs in
       let d2'' = BExp.par_subs sigs' d2' in
       let d = [(d1' |. d2'')] in
       let x' = (r1,s1,d,a1,b1) in
       let rho = get_rho sigs in
       let x'' : r = whole_subs rho x' in
       Some x''
  in

  let res = unify_contract print_ret unify _X _Y in

  if List.length _X' + List.length _Y' < List.length res then
    begin
      pn_s "JOIN" "\n@@ _join reduces\n";
      dbg "JOIN" "|X|:" pi (List.length _X');
      dbg "JOIN" "|Y|:" pi (List.length _Y');
      dbg "JOIN" "|res|:" pi (List.length res);
      pn_s "JOIN" "~~##--##--##~~##--##--##~~"
    end;
  res
;;


let rec amp_substitute ed by _P =
  let subbd = amp_substitute ed by in
  let subt = Term.substitute (_T ed) (_T by) in
  let subb = BExp.substitute (_T ed) (_T by) in
  let subv v = if v = ed then by else v in

  let rec subst_init ed by = function
      Block.INIT_E -> Block.INIT_E
    | Block.INIT_S t -> Block.INIT_S (subt t)
    | Block.INIT_M ids -> Block.INIT_M (subst_init ed by |>>| ids)
  in
  
  match _P with
    ASSIGN (_x, _t, l) ->
     let _x' = subv _x in
     let _t' = subt _t in
     ASSIGN (_x', _t', l)
  | IF (_b, _P1, _P2, l) ->
     let _b' = subb _b in
     let _P1' = subbd _P1 in
     let _P2' = subbd _P2 in
     IF (_b', _P1', _P2', l)
  | COMP (_P1, _P2, l) ->
     let _P1' = subbd _P1 in
     let _P2' = subbd _P2 in
     COMP (_P1', _P2', l)
  | MALLOC (_x, _y, l) ->
     let _x' = subv _x in
     let _y' = Exp.substitute ed by _y in
     MALLOC (_x', _y', l)
  | SARRAY (_x, _y, _z, l) ->
     SARRAY (_x, _y, _z, l)
  | LOOKUP (_x, _p, _f, l) ->
     begin
       match _f, _p with
         "*", Term.EXP ((Exp.VAR _) as v) when v = ed ->
          ASSIGN (_x, _T by, l)
       | _ ->
          let _x' = subv _x in
          let _p' = subt _p in
          LOOKUP (_x', _p', _f, l)
     end
  | MUTATION (_p, _f, _t, l) ->
     begin
       let _p' = subt _p in
       let _t' = subt _t in
       match _f, _p with
         "*", Term.EXP ((Exp.VAR _) as v) when v = ed ->
          ASSIGN (by, _t', l)
       | _ ->
          MUTATION (_p', _f, _t', l)
     end
  | DISPOSE (_x, l) ->
     let _x' = subt _x in
     DISPOSE (_x', l)
  | WHILE (_b, _bs, _P1, l) ->
     let _b' = subb _b in
     let _bs' = subb |>>| _bs in
     let _P1' = subbd _P1 in
     WHILE (_b', _bs', _P1', l)
  | PROCCALL (_x, _args, l) ->
     let _args' = subt |>>| _args in
     PROCCALL (_x, _args', l)
  | BLOCK (dc, _P1, l) ->
     let _P1' = subbd _P1 in
     let dc' = subbd |>>| dc in
     BLOCK (dc', _P1', l)
  | DECL (_x, _len, _data, l) ->
     let _len' = subt |>>| (_T |>>| _len) in
     let _data' = subst_init ed by _data in
     DECL (_x, Term.toExp |>>| _len', _data', l)
  | RETURN (_x, l) ->
     let _x' = subt _x in
     RETURN (_x', l)
  | SKIP l ->
     SKIP (l)
  | LABEL (lbl, el, l) ->
     let el' = (fun e -> if e = Exp.toStr ed then Exp.toStr by else e) |>>| el in
     LABEL (lbl, el', l)
  | FAIL -> FAIL

let rec star_substitute ed by _P =
  let subbd = star_substitute ed by in
  let subt = Term.substitute (_T ed) by in
  let subb = BExp.substitute (_T ed) by in

  let rec subst_init ed by = function
      Block.INIT_E -> Block.INIT_E
    | Block.INIT_S t -> Block.INIT_S (subt t)
    | Block.INIT_M ids -> Block.INIT_M (subst_init ed by |>>| ids)
  in

  match _P with
    ASSIGN (_x, _t, l) ->
     let _t' = subt _t in
     ASSIGN (_x, _t', l)
  | IF (_b, _P1, _P2, l) ->
     let _b' = subb _b in
     let _P1' = subbd _P1 in
     let _P2' = subbd _P2 in
     IF (_b', _P1', _P2', l)
  | COMP (_P1, _P2, l) ->
     let _P1' = subbd _P1 in
     let _P2' = subbd _P2 in
     COMP (_P1', _P2', l)
  | MALLOC (_x, _y, l) ->
     let _y' = Exp.substitute ed (Term.toExp by) _y in
     MALLOC (_x, _y', l)
  | SARRAY (_x, _y, _z, l) ->
     SARRAY (_x, _y, _z, l)
  | LOOKUP (_x, _p, _f, l) ->
     LOOKUP (_x, _p, _f, l)
  | MUTATION (_p, _f, _t, l) ->
     let _t' = subt _t in
     MUTATION (_p, _f, _t', l)
  | DISPOSE (_x, l) ->
     DISPOSE (_x, l)
  | WHILE (_b, _bs, _P1, l) ->
     let _b' = subb _b in
     let _bs' = subb |>>| _bs in
     let _P1' = subbd _P1 in
     WHILE (_b', _bs', _P1', l)
  | PROCCALL (_x, _args, l) ->
     let _args' = subt |>>| _args in
     PROCCALL (_x, _args', l)
  | BLOCK (dc, _P1, l) ->
     let _P1' = subbd _P1 in
     let dc' = subbd |>>| dc in
     BLOCK (dc', _P1', l)
  | DECL (_x, _len, _data, l) ->
     let _len' = subt |>>| (_T |>>| _len) in
     let _data' = subst_init ed by _data in
     DECL (_x, Term.toExp |>>| _len', _data', l)
  | RETURN (_x, l) ->
     let _x' = subt _x in
     RETURN (_x', l)
  | SKIP l ->
     SKIP (l)
  | LABEL (lbl, el, l) ->
     let el' = (fun e -> if e = Exp.toStr ed then Term.toStr by else e) |>>| el in
     LABEL (lbl, el', l)
  | FAIL -> FAIL


let bar x =
  let v' = Exp.set_bar x in
  _T v'

let hat x =
  let v' = Exp.set_hat x in
  _T v'

let rem_unsat _X l =
  (fun (_s, _d, _A, _, _) ->
    let fm = conj _s _d _A in
    VcpVBase.check_sat2 fm ) |>- _X

let amp_star_contract (s, (exs,pures,ptrs,preds)) =
  let aux (s, ptrs) ((pt, fields) as ptr) =
    match pt, fields with
      Term.EXP (Exp.ADDR v), ("*",x)::_ ->
       let s' = subs v x s in
       (s', ptrs)
    | _ ->
       (s, ptrs @ [ptr])
  in
  let (s',ptrs') = aux |->> (s, ptrs) in
  (s', (exs,pures,ptrs',preds))

let rec get_amp_term = function
    Term.NULL -> []
  | Term.EXP exp ->
     match exp with
       Exp.ADDR ((Exp.VAR _) as v) -> [v]
     | _ -> []

let get_amp_bexp = function
  | BExp.UNIT (t1, _, t2) ->
     get_amp_term t1 @@ get_amp_term t2
  | _ -> []

let rec get_amp_init = function
    Block.INIT_E -> []
  | Block.INIT_S t -> get_amp_term t
  | Block.INIT_M ids -> List.concat (get_amp_init |>>| ids)
       
let rec get_amp = function
    ASSIGN (x, e, _) -> get_amp_term e
  | IF (b, p1, p2, _) ->
     let v1 = get_amp_bexp b in
     let v2 = get_amp p1 in
     let v3 = get_amp p2 in
     (v1 @@ v2 @@ v3)
  | COMP (p1, p2, _) ->
     let v1 = get_amp p1 in
     let v2 = get_amp p2 in
     (v1 @@ v2)
  | MALLOC (v, l, _) ->
     []
  | SARRAY (v, e, l, _) ->
     []
  | LOOKUP (v, e, _, _) ->
     []
  | MUTATION (e1, _, e2, l) ->
     get_amp_term e2
  | DISPOSE (e, _) ->
     []
  | WHILE (b, _, p, _) ->
     get_amp_bexp b @@ get_amp p
  | SKIP _ ->
     []
  | PROCCALL (_, args, _) ->
     concat (get_amp_term |>>| args)
  | BLOCK (dc, p, _) ->
     concat (get_amp |>>| dc) @@ get_amp p
  | RETURN (t, _) ->
     get_amp_term t
  | DECL (v, lens, data, _) ->
     get_amp_init data
  | LABEL (_,_,_) | FAIL -> []


let rec free_mod_v = function
    ASSIGN (x, e, _) ->
     (x::Term.fv e, get_amp_term e @@ [x])
  | IF (b, p1, p2, _) ->
     let (p1_fv, p1_mv) = free_mod_v p1 in
     let (p2_fv, p2_mv) = free_mod_v p2 in
     (BExp.fv b @@ p1_fv @@ p2_fv, p1_mv @@ p2_mv)
  | COMP (p1, p2, _) ->
     let (p1_fv, p1_mv) = free_mod_v p1 in
     let (p2_fv, p2_mv) = free_mod_v p2 in
     (p1_fv @@ p2_fv, p1_mv @@ p2_mv)
  | MALLOC (v, e, _) ->
     (v :: Exp.fv e, [v])
  | SARRAY (v, e, l, _) ->
     (v :: Term.fv e, [v])
  | LOOKUP (v, e, _, _) ->
     (v :: Term.fv e, [v])
  | MUTATION (e1, _, e2, l) ->
     (Term.fv e1 @@ Term.fv e2, [])
  | DISPOSE (e, _) ->
     (Term.fv e, [])
  | WHILE (b, _, p, _) ->
     let (p_fv, p_mv) = free_mod_v p in
     (BExp.fv b @@ p_fv, p_mv)
  | SKIP _ ->
     ([], [])
  | PROCCALL (_, args, _) ->
     (concat (Term.fv |>>| args), [])
  | BLOCK (dc, p, _) ->
     let res = free_mod_v |>>| dc in
     let (fvs, mvs) = List.split res in
     let (p_fv, p_mv) = free_mod_v p in
     (p_fv @@ concat fvs, p_mv @@ concat mvs)
  | RETURN (t, _) ->
     (Term.fv t, [])
  | DECL (v, lens, _, _) ->
     (concat (Exp.fv |>>| lens), []) (* question *)
  | LABEL (_,_,_) | FAIL -> ([], [])

let rec to_disjunctive_normal = function (** (A || B) && (C || D) -> ((A || B) && C) || ((A || B) && D) *)
  | BExp.OP (BExp.OP (b, Op.OR, c), Op.AND, a)
    | BExp.OP (a, Op.AND, BExp.OP (b, Op.OR, c)) ->
     let a' = to_disjunctive_normal a in
     let b' = to_disjunctive_normal b in
     let c' = to_disjunctive_normal c in
     let d  = ((a' &. b') |. (a' &. c')) in (** A && (B || C) -> (A && B) || (A && C) *)
     to_disjunctive_normal d
  | x -> x

let approx b =
  VcpVBase.peano_to_pb_b $$ to_disjunctive_normal b
(* approx_unknown_bexp $$ to_disjunctive_normal b *)

let subs_string_term _s _A _t =
  let (_t', s_subs, len) =
    match _t with
      Term.NULL -> (Term.NULL, None, 0)
    | Term.EXP e ->
       let subs_string_exp _e =
         match _e with
           Exp.STRING s ->
            let new_prog_var = __E (new_prog_var (), []) in
            let n = Bytes.length s in
            (new_prog_var, Some (new_prog_var, Term.EXP (_C n)), n)
         | Exp.FCALL (s,ts) -> (Exp.FCALL (s, ts), None, 0)
         | e -> (e, None, 0)
       in
       let (e', m, n) = subs_string_exp e in
       (Term.EXP e', m, n)

  in
  match s_subs with
    None -> (_t', _s, _A, [])
  | Some (x, n) ->
     let a_hat = _T (Exp.set_hat (newvar [])) in (** Later we will add CHAR here *)
     let _s' = subs x a_hat _s in
     let last_1 = Term.op a_hat n Op.ADD in
     let last = Term.op a_hat (Term.op n (Term.EXP (_C 1)) Op.ADD) Op.ADD in
     let _D = ("Stringpart", [a_hat; last_1]) in
     let cell = (last, [("*", Term.zero)]) in
     if len > 0 then
       let _A' = (fun (a,b,c,d) -> (a,b,c @ [cell],d @ [_D])) _A in
       (_T x, _s', _A', [(x, cell, _D)])
     else
       let _A' = (fun (a,b,c,d) -> (a,b,c @ [cell],d)) _A in
       (_T x, _s', _A', [(x, cell, _D)])

let get_structure structures name =
  try
    V.find name structures
  with
    _ ->
    pn "All structures:\n----------------";
    V.iter (fun name _ -> pw name) structures;
    raise (StError ("Exception: Structure " ^ name ^ " is not found"))

let is_list_type t packs =
  let (_, _, _, _, structures, _) = packs in
  if Term.with_head t then
    let v = Term.head "" t in
    if Exp.is_struct v then
      let s = Exp.get_struct_name v in
      let ((_, _, tp) as st) =
        try
          get_structure structures s
        with
          e ->
          pn "<- is_list_type";
          raise e
      in
      dbg "LIST" "The Struct:" Structure.pprint st;
      match tp with
      | Some (dt) when "next" |<- (Exp.toStr|>>|dt) -> true
      | Some (flds) -> List.length flds = 1
      | _ -> false
    else
      false
  else
    false

let term_to_int = (function Term.EXP (Exp.CONST i) -> i | _ -> raise (StError "Array dimension is not integer"))
let exp_to_int  = (function Exp.CONST i -> i | _ -> raise (StError "Array dimension is not integer"))

                    (*

let rec var_size packs var : int =
  let n_to_1 il = (fun a i -> a * i) |->> (1, il) in
  if Exp.is_struct var then
    begin
      let sn = Exp.get_struct_name var in
      let (_, fields, _) = get_structure packs sn in
      let field_size = (fun acc (fn,_) ->
          let sz =
            if Exp.is_struct fn && not (Exp.is_ptr fn) then
              begin
                let sz' = var_size packs fn in
                if Exp.is_array fn then
                  sz' * n_to_1 (exp_to_int |>>| Exp.get_array_length fn)
                else
                  sz'
              end
            else
              if Exp.is_array fn then
                n_to_1 $$ (exp_to_int |>>| Exp.get_array_length fn)
              else
                0
          in
          acc + sz
        ) |->> (0, fields) in
      field_size + 1
    end
  else
    1

let rec _AllocType packs _x var _n : Pointer.t list =
  let _x_n = _x @+@ _n in
  (**  ("Array", [_x; _x_n @-@ (_T (_C 1))]) *)
  match _n with
    Term.EXP (Exp.CONST _c) ->
     begin
       dbg "ALLOC" "ALLOC @ c:" pi _c;
       let sn = Exp.get_struct_name var in
       let (_, fields, _) = get_structure packs sn in
       dbg "ALLOC" "fields:" (iterS (fun (a,_) -> Exp.pprint a) ",") fields;
       let t_fields, s_fields = List.partition (fun (fld, _) -> Exp.is_struct (__V fld) && not (Exp.is_ptr (__V fld))) fields in
       dbg "ALLOC" "t_fields:" (iterS (fun (a,_) -> Exp.pprint a) ",") t_fields;
       dbg "ALLOC" "s_fields:" (iterS (fun (a,_) -> Exp.pprint a) ",") s_fields;
       let _k = (fun acc (fld,_) -> acc + var_size packs fld) |->> (0, fields) in
       dbg "ALLOC" "k:" pl _k;
       let rec aux j u d =
         if j <= u then
           begin
             dbg "ALLOC" "j:" pl j;
             let _kj1 = _x_n @+@ _T (_C ((j-1)*_k)) in

             let s_fields'' = (fun acc (fld, v) ->
                 let x_tld = Term.encode (Exp.set_tilde $$ newvar (Exp.get_attributes fld)) in
                 acc@[(Exp.to_str fld, x_tld)]
               ) |->> ([], s_fields) in

             let t_fields'', allocs =
               if List.length t_fields > 0 then
                 let field1 = List.hd t_fields in
                 let fld1 = fst field1 in
                 let one = _T (_C 1) in
                 let alloctype_1 = _AllocType packs _kj1 fld1 one in

                 let t_fields'', allocs, _, _ =
                   (fun (acc1, acc2, fldi_1, _kji_1) ((fldi : Exp.t), _) ->
                     let fldi_1_size : int = var_size packs fldi_1 in
                     let _kji = _kji_1 @-@ (_T (_C fldi_1_size)) in
                     let alloctype_i = _AllocType packs _kji fldi one in
                     (acc1 @ [(Exp.to_str fldi, _kji)], acc2 @ alloctype_i, fldi, _kji)
                   ) |->> (([(Exp.to_str fld1, _kj1)], alloctype_1, fld1, _kj1), List.tl t_fields) (** i in 1 to l *)
                 in
                 t_fields'', allocs
               else
                 [],[]
             in

             let _x_j = _x @+@ _T (_C (j-1)) in
             let cell = (_x_j, t_fields'' @ s_fields'') in
             dbg "ALLOC" "cell:" Pointer.pprint cell;
             d @ (cell :: allocs)
           end
         else
           d
       in
       let r1 = aux 1 _c [] in
       r1
     end
  | _ ->
     pn_s "ALLOC" "No allocation";
     []

let alloc_type structs _x _sigma _t =
  if Exp.is_struct _sigma then
    begin
      let ptrs = _AllocType structs _x _sigma _t in
      dbg "ALLOC" "ALLOC(if..then):" (iterS Pointer.pprint "*") ptrs;
      (ptrs, [])
    end
  else
    begin
      let cells = [("Array", [_x; (_x @+@ (_t @-@ (_T (_C 1))))])] in
      dbg "ALLOC" "ALLOC(else):" (iterS Predicate.pprint "*") cells;
      ([], cells)
    end
                     *)
  
let is_var_temp = function
    Exp.VAR (v,_) ->
    Bytes.length v > 2 &&
      Bytes.sub v 0 2 = "#_"
  | _ -> false

let contains_no_question (_,pures,ptrs,preds) =
  let q_pures = List.for_all (contains_no_undef_in_bexp) pures in
  let hds = (fst |>>| ptrs) in
  let q_hds  = List.for_all (fun h -> contains_no_undef_in_term h) hds in
  let q_ptrs  = List.for_all (contains_no_undef_in_term) ((snd |>>| (concat (snd |>>| ptrs)))) in
  let q_pred = List.for_all (contains_no_undef_in_term) (concat (snd |>>| preds)) in
  q_pures && q_hds && q_ptrs && q_pred

let sanitize s ts =
  (fun s t ->
    match t with
      Term.EXP ((Exp.VAR _) as ev) when is_var_temp ev -> M.remove ev s
    | _ ->
       let fvs = Term.fv t in
       (fun s (v : Exp.t) -> if is_var_temp v then M.remove v s else s) |->> (s, fvs)
  ) |->> (s, ts)

let combine_res res =
  res

let to_spec s0 (r,s,d,a,b) =
  let keep_only_global_n_param_s s = M.filter (fun key _ ->
                                         match key with
                                           Exp.VAR _ as key' ->
                                             Exp.is_global key' || Exp.is_param key'
                                         | _ -> false
                                       ) s in
  let remove_control_vars s = M.filter (fun key _ ->
                                  match key with
                                    Exp.VAR key' ->
                                    let skey = fst key' in
                                    not (skey = "$return" || skey = "$break" || skey = "$continue")
                                  | _ -> false
                                ) s in

  let s0' = remove_control_vars s0 in
  let s' = keep_only_global_n_param_s s in
  
  (r, (s0', d, b), (s', d, a))

let print_specs count fname (u', s', d, (a: Formula.ut), b) =
  if fname = !Options.functions || "PRECOND" |<- !Ftools.p_opt then
    begin
      pn ("Disjunct " ^ (string_of_int count) ^ ":");
    end;
  
  if fname = !Options.functions || "PRECOND" |<- !Ftools.p_opt then
    begin
      p "r: "; Term.pprint u'; pn ";";
      p "s: "; m_print_s s'; pn ";";
      p "d: "; if List.length d > 0 then iterS BExp.pprint " & " d else p "True"; pn ";";
      p "A: "; Formula.pprint [a]; pn ";";
      p "B: "; Formula.pprint [b]; pn ".\n";
    end;
;;
  
let make_spec res returns' s fname gt1 ds =
  
  let count = ref 1 in

  let returns = returns' in
  if fname = !Options.functions || "PRECOND" |<- !Ftools.p_opt then
    begin
      pn ("\nNumber of disjuncts: " ^ (string_of_int (List.length returns)) ^ " for " ^ fname^ "\n")
    end;

  let res2 = (fun ((u', s', d, (a: Formula.ut), b) as rets) ->
      print_specs !count fname (u', s', d, (a: Formula.ut), b);
      count.contents <- (!count + 1);
      to_spec s rets
    ) |>>| returns
  in

  let gt2 = Sys.time () in
  let gtm = gt2 -. gt1 in
  let gtm' = (ceil (gtm *. 1000.0)) /. 1000.0 in
  let req_tm = string_of_float gtm' in
  pn_s "PRECOND" ("Time: " ^ req_tm ^ " sec.");
  res2, ds

let res_maker s_subs = (fun (_s'', _d'', _A'', _B'', _v'', _) ->
    let _s', _A' =
      (fun (_s', _A') (x, _pt, _D) ->
        M.remove x _s', (fun (a,b,c,d) -> (a,b,(fun c'->not(c'=_pt)) |>- c,(fun d' -> not (snd d'= snd _D)) |>- d)) _A') |->> ((_s'', _A''), s_subs) in
    (_s', _d'', _A', _B'', _v''))

let false_d : d = (_False, _False, _False)
                
let create_fields _t at _f packs =
  let fields =  (** @Jul29 *)
    if Term.with_head _t then
      let hd = Term.head (Term.toStr _t) _t in
      if Exp.is_ptrptr hd then
        begin
          pn_s "LOOKUP" "PTRPTR mode";
          if Exp.is_struct hd then
            [__E ("*",[Exp.STRUCT (Exp.get_struct_name hd); Exp.PTR])]
          else
            [__E ("*",[Exp.PTR])]
        end
      else if Exp.is_struct hd then
        begin
          pn_s "LOOKUP" "STRUCT mode";
          let st = Exp.get_struct_name hd in
          let (_, _, _, _, (structs : Structure.t V.t), _) = packs in
          let (_, fields, _) = try
              get_structure structs st
            with
              e ->
              pn "<- create_fields";
              raise e
          in
          (fst |>>| fields)
        end
      else
        begin
          pn_s "LOOKUP" "PTR mode";
          [__E ("*",[])]
        end
    else
      raise (StError "CREATE FIELD fails: no head")
  in
  let (_, attr) = try
      let e' : Exp.t = List.find (fun fld -> fst (__V fld) = _f) fields in
      __V e'
    with _ -> (_f, []) in
  let _z_bar = _T (newvar (at::attr)) in
  dbg "LOOKUP" "z~ :" Term.pprint _z_bar;
  let fields' = (function Exp.VAR (fld, attr) ->
                           if _f = fld then
                             begin
                               (_f, _z_bar)
                             end
                           else
                             let z_bar = _T (newvar (at::attr)) in
                             (fld, z_bar)
                        | _ -> raise (NotAVariable "create fields")
                ) |>>| fields in
  dbg "LOOKUP" "FLD:" Pointer.pprint (_z_bar, fields');
  (_z_bar, fields')

let offset x n =
  let one = _T $$ Exp.CONST 1 in
  x @+@ (n @-@ one)
               
let (+~~) x i =
  _T $$ Exp.op x (Exp.CONST i) Op.ADD

let (+-~) x i =
  offset (_T x) (_T $$ _C i)

(* let __alloc_type_sigma x =
  ([], [])
 *)

let get_only_fields structs _x =
  let st_name = Exp.get_struct_name _x in
  let (_, fields', _) = try
      V.find st_name structs
    with
      e ->
      pw "Not found struct:"; Exp.print _x; pn " in";
      V.iter (fun k v -> pw k; pw ", ") structs;
      raise e
  in
  let fields = fst |>>| fields' in
  fields

let get_only_fields2 structs _tau =
  try
    let (_, fields', _) =
      V.find _tau structs in
    let fields = fst |>>| fields' in
    fields
  with
    e -> []
   

  
let is_only_struct _x =
  Exp.is_struct _x && not (Exp.is_ptr _x)
  
let __alloc_type_sigma (xT: Term.t) _s _L n = (** x must be fresh variable *)
     ([],[("Array", [xT; offset xT (eval _s _L n)])])

  
let __alloc_type_sigma_static x _s _L = function
    Term.EXP (Exp.CONST 1) -> ([(x, [("*", Term.zero)])], [])
  | n ->
     let n' = eval _s _L n in
     ([],[("Array", [x; offset x n'])])

  
let __alloc_type_sigma_init (x:Exp.t) _s _L init =
  let fld = "*" in
  match init with
    Block.INIT_M ids ->
     let ptrs = List.mapi (fun i id ->
                    match id with
                      Block.INIT_S t ->
                       let t' = eval _s _L  t in
                      (x +~~ i, [(fld, t')])
                    | _ -> raise (StError "Wrong Type of init data")
                  ) ids
     in
     (ptrs, [])
  | Block.INIT_S t ->
     let t' = eval _s _L t in
     let cell = (_T x, [("*", t')]) in
     ([cell], [])
  | _ ->
     raise (StError "Unsupported Array Length")

let rec fold_n f i =
  if i = 0 then
    []
  else
    (
      f i () :: fold_n f (i-1) 
    )
(*

  
let rec __alloc_type_struct_static structs x (fields : Exp.t list) n =
  let cell_nv_pairs () : (Exp.t * Exp.t) list = (fun cells (fld : Exp.t) ->
      let nv = newvar [Exp.HAT] in
      cells @ [(fld, nv)]
    ) |->> ([], fields) in
  let f i : (Term.t * (Exp.t * Exp.t) list) = ((x +-~ i), cell_nv_pairs ()) in
  let ptrs' : (Term.t * (Exp.t * Exp.t) list) list = fold_n f n in
  let pairs : (Exp.t * Exp.t) list = List.concat (snd |>>| ptrs') in
  let ptrs = (fun (a,b) ->
      let b' = (fun (c,d) -> (Exp.to_str c, _TT d)) |>>| b in
      (a, b')) |>>| ptrs' in
  let other_ptrs, other_preds = (fun (ptrs, preds) (fld, k) ->
      if Exp.is_struct fld && Exp.is_array fld then
        let st_name = Exp.get_struct_name fld in
        let lens = Exp.get_array_length fld in
        let (_, fields'', _) = V.find st_name !structs in
        let fields' = fst |>>| fields'' in
        let (ptrs', preds') = __alloc_type_struct_static_n structs k fields' lens in
        (ptrs @ ptrs', preds @ preds')
      else if Exp.is_struct fld then
        let st_name = Exp.get_struct_name fld in
        let (_, fields'', _) = V.find st_name !structs in
        let fields' = fst |>>| fields'' in
        let (ptrs', preds') = __alloc_type_struct_static structs k fields' 1 in
        (ptrs @ ptrs', preds @ preds')
      else if Exp.is_array fld then
        let lens = Exp.get_array_length fld in
        let lens' = _T |>>| (_C |>>| lens) in
        let (ptrs', preds') = __alloc_type_sigma_n k lens' in
        (ptrs @ ptrs', preds @ preds')
      else
        let (ptrs', preds') = __alloc_type_sigma k in
        (ptrs @ ptrs', preds @ preds')
    ) |->> (([],[]), pairs) in
  (ptrs @ other_ptrs, other_preds)

and __alloc_type_struct_static_n structs x fields = function
    [] ->
     __alloc_type_struct_static structs x fields 1
  | [n] ->
     __alloc_type_struct_static structs x fields n
  | n::ns ->
     let f j =
       let kj = newvar [Exp.HAT] in
       let cell = (x +-~ j, [("*", _TT kj)]) in
       let (ptrs, preds) = __alloc_type_struct_static_n structs kj fields ns in
       (cell::ptrs, preds)
     in
     (fun (a,b) (a',b') -> (a@a', b@b')) |->> (([],[]), fold_n f n)
 *)

let rec __alloc_type_struct_init init_data is_static structs (x : Exp.t) (fields : Exp.t list) _s _L (n : int) =

  let zero = Block.INIT_S (Term.EXP (Exp.CONST 0)) in
  dbg "DECL" "x:" Exp.pprint x;
  
  let cell_nv_pairs idata : (Exp.t * Term.t * Block.init) list =
    dbg "DECL" "idata(cell_nv_pairs):" Block.print_init idata;
    match idata with
      Block.INIT_M ids ->
       let pairs = List.combine fields ids in
       let cell = (fun (fld, id) ->
           match id with
             Block.INIT_S t ->
              let t' = eval _s _L t in
              (fld, t', Block.INIT_E)
           | _ ->
              let nv = newvar [Exp.HAT] in
              (fld, _T nv, id)
         ) |>>| pairs in
       cell
    | Block.INIT_S t ->
       let t' = eval _s _L t in
       let hd_fld = List.hd fields in
       let rest_fld = List.tl fields in
       let hd_fld_dt = (hd_fld, t', idata) in
       let rest_fld_dt = (fun f ->
         let nv = _T $$ newvar [Exp.HAT] in
         (f, nv, zero)
         ) |>>|rest_fld in
       hd_fld_dt :: rest_fld_dt
    | _ ->
       raise (StError "Error: cell_nv_pairs")
      (*
      (fun cells (fld : Exp.t) ->
        match idata with
          Block.INIT_S t ->
           cells @ [(fld, t, Block.INIT_E)]
        | _ ->
           let nv = newvar [Exp.HAT] in
           cells @ [(fld, _TT nv, idata)]
      ) |->> ([], fields) *)
  in
  
  
  match init_data with
    Block.INIT_E
  | Block.INIT_S _ -> raise (StError "Wrong initializing data")
  | Block.INIT_M ids ->

     dbg "DECL" "ids:" Block.print_init init_data;
     
     let f (i : int) () : (Term.t * (Exp.t * Term.t * Block.init) list) =
       let i_data = List.nth ids (i-1) in
       dbg "DECL" "f(i):" pl i;
       dbg "DECL" "i_data:" Block.print_init i_data;
       ((x +-~ i), cell_nv_pairs i_data)
     in

     dbg "DECL" "n:" pi n;
     
     let ptrs' : (Term.t * (Exp.t * Term.t * Block.init) list) list =
       if n > 1 then
         (
           pn_s "DECL" "array";
           fold_n f n
         )
       else
         (
           pn_s "DECL" "non-array";
           [(_T x, (cell_nv_pairs init_data))]
         )
     in
     let pairs : (Exp.t * Term.t * Block.init) list = List.concat ((snd |>>| ptrs')) in
     let ptrs : Pointer.t list = (fun (a,b) ->
         let b' = (fun (c,d,_) -> (Exp.toStr c, d)) |>>| b in
         (a, b')) |>>| ptrs' in

     dbg "DECL" "ptrs:" (iterS Pointer.pprint "*") ptrs;
     dbg "DECL" "|pairs|:" pl (List.length pairs);
     
     let other_ptrs, other_preds = (fun (ptrs, preds) (fld, k', idata) ->
         dbg "DECL" "Field:" Exp.pprint fld;
         dbg "DECL" "s(t)::" Term.pprint k';
         dbg "DECL" "idata:" Block.print_init idata;
         pn_s "DECL" "-----";
         match k' with
         | Term.EXP (Exp.CONST _) ->
            (ptrs, preds)
         | Term.EXP (k) ->
            
            if is_only_struct fld && Exp.is_array fld then
              let st_name = Exp.get_struct_name fld in
              let lens = exp_to_int |>>| Exp.get_array_length fld in
              let (_, fields'', _) = V.find st_name structs in
              let fields' = fst |>>| fields'' in
              let (ptrs', preds') = __alloc_type_struct_init_n idata is_static structs k fields' _s _L lens in
              (ptrs @ ptrs', preds @ preds')
            else if is_only_struct fld then
              let st_name = Exp.get_struct_name fld in
              let (_, fields'', _) = V.find st_name structs in
              let fields' = fst |>>| fields'' in
              let (ptrs', preds') = __alloc_type_struct_init idata is_static structs k fields' _s _L 1 in
              (ptrs @ ptrs', preds @ preds')
            else if Exp.is_array fld then (
              try
                let lens = exp_to_int |>>| Exp.get_array_length fld in
                let (ptrs', preds') = __alloc_type_struct_init_n idata is_static structs k [] _s _L lens in
                (ptrs @ ptrs', preds @ preds')
              with
                StError "Unsupported Array Length" -> (ptrs, preds)
              | e -> raise e
            )
            else
              (ptrs, preds)
         | Term.NULL ->
            (ptrs, preds)
         (* | _ ->
            Term.pprint k';
            raise (StError "Error: more cells") *)
       ) |->> (([],[]), pairs) in
     (ptrs @ other_ptrs, other_preds)
     
and __alloc_type_struct_init_n init_data is_static structs (x:Exp.t) fields _s _L = function
    [] ->
     if List.length fields > 0 then
       __alloc_type_struct_init init_data is_static structs x fields _s _L 1
     else
       (
         __alloc_type_sigma_init x _s _L init_data
       )
  | [n] ->
     if List.length fields > 0 then
       begin
         dbg "DECL" "Switching to " Exp.pprint x;
         __alloc_type_struct_init init_data is_static structs x fields _s _L n
       end
     else
       (
         __alloc_type_sigma_init x _s _L init_data
       )
  | n::ns ->
     begin
       match init_data with
         Block.INIT_M ids ->
         dbg "DECL" "|dims|" pl (List.length ns + 1);
         let f j () =
           let kj = newvar [Exp.HAT] in
           let cell = (x +-~ j, [("*", _T kj)]) in
           dbg "DECL" "Exploring for " Exp.pprint kj;
           let init_data' = List.nth ids (j-1) in
           dbg "DECL" "Mi:" Block.print_init init_data' ;
           let (ptrs, preds) = __alloc_type_struct_init_n init_data' is_static structs kj fields _s _L ns in
           (cell::ptrs, preds)
         in
         (fun (a,b) (a',b') -> (a@a', b@b')) |->> (([],[]), fold_n f n)
       | _ -> raise (StError "Incompatible Init Data")
     end

let rec __alloc_type_struct  is_static structs x (fields : Exp.t list) _s _L n =
  let cell_nv_pairs () : (Exp.t * Exp.t) list = (fun cells (fld : Exp.t) ->
      let nv = newvar [Exp.HAT] in
      cells @ [(fld, nv)]
    ) |->> ([], fields) in
  let f i () : (Term.t * (Exp.t * Exp.t) list) = ((x +-~ i), cell_nv_pairs ()) in
  let ptrs' : (Term.t * (Exp.t * Exp.t) list) list = fold_n f n in
  let pairs : (Exp.t * Exp.t) list = List.concat (snd |>>| ptrs') in
  let ptrs = (fun (a,b) ->
      let b' = (fun (c,d) ->
          if Exp.is_struct c || Exp.is_array c then
            (Exp.toStr c, _T d)
          else
            if is_static then
              (Exp.toStr c, _T (_C 0))
            else
              (Exp.toStr c, _T d)
        ) |>>| b in
      (a, b')
    ) |>>| ptrs' in
  let other_ptrs, other_preds = (fun (ptrs, preds) (fld, k) ->
      if is_only_struct fld && Exp.is_array fld then
        let st_name = Exp.get_struct_name fld in
        let lens = exp_to_int |>>| Exp.get_array_length fld in
        let (_, fields'', _) = V.find st_name structs in
        let fields' = fst |>>| fields'' in
        let (ptrs', preds') = __alloc_type_struct_n is_static structs k fields' _s _L lens in
        (ptrs @ ptrs', preds @ preds')
      else if is_only_struct fld then
        let st_name = Exp.get_struct_name fld in
        let (_, fields'', _) = V.find st_name structs in
        let fields' = fst |>>| fields'' in
        let (ptrs', preds') = __alloc_type_struct is_static structs k fields' _s _L 1 in
        (ptrs @ ptrs', preds @ preds')
      else if Exp.is_array fld then
        let lens = exp_to_int |>>| Exp.get_array_length fld in
        let (ptrs', preds') = __alloc_type_struct_n is_static structs k [] _s _L lens in
        (ptrs @ ptrs', preds @ preds')
      else
        (ptrs, preds)
    ) |->> (([],[]), pairs) in
  (ptrs @ other_ptrs, other_preds)

and __alloc_type_struct_n is_static structs x fields _s _L (nss : int list) =
  match nss with
    [] ->
     __alloc_type_struct is_static structs x fields _s _L 1
  | ([n]: int list) ->
     if List.length fields > 0 then
       __alloc_type_struct is_static structs x fields _s _L n
     else
       __alloc_type_sigma (_T x) _s _L (_T $$ _C n)
  | n::ns ->
     let f j () =
       let kj = newvar [Exp.HAT] in
       let cell = (x +-~ j, [("*", _T kj)]) in
       let (ptrs, preds) = __alloc_type_struct_n is_static structs kj fields _s _L ns in
       (cell::ptrs, preds)
     in
     (fun (a,b) (a',b') -> (a@a', b@b')) |->> (([],[]), fold_n f n)


let is_void_pointer attrs =
  List.exists (function Exp.FUNC (ret_attrs,_) ->
                         List.length ret_attrs = 1 && List.hd ret_attrs = Exp.PTR
                      | _ -> false) attrs
    
let rec precond (_s, _d, _A, _L) (packs : pck) l_X _P : (o list * r list * d) =
  let comp l p1 p2 =
    COMP (p1, p2, l)
  in
  let (_, _, _, _, (structs : (Structure.t V.t)), _) = packs in
  all_struct := structs;
  EL.all_struct := structs;
  
  let precond_decl _x lens (init_data : Block.init) l =
    (** function to compute (x + (z-1)) *)

    (** Flatten size for multidimensional array *)
    (* let n = (fun acc len ->
        match eval _s _L len with
          Term.EXP (Exp.CONST n') -> acc * n'
        | _ -> acc (** should raise an exception *)
      ) |->> (1, lens) in *)

    (** a-hat *)
    
    let _a_hat = Term.toExp ((* Exp.set_hat (newvar (Exp.get_attributes _x)) *)
      (* try
        M.find _x _s
      with
        _ -> *)
         let s_x = Exp.toStr _x in 
         if s_x |<- !all_functions then
           if F.mem s_x !f_heap then
             F.find s_x !f_heap
           else
             add_f s_x
         else
           _T $$ Exp.set_hat (newvar (Exp.get_attributes _x)))
        (* raise (StError ("Not found " ^ (Exp.toStr _x))) *)
    in
    (** s[x:=a-hat] *)
    
    (* let _n : Term.t list = _T |>>| (_C |>>| lens) in *)
    
    let __is_only_struct = is_only_struct _x in
    let __is_array = List.length lens > 0 in
    let __is_static = Exp.is_static _x in
    let __is_with_init_data = init_data <> Block.INIT_E in
     
    dbg "DECL" "Var:" Exp.pprint _x;
    dbg "DECL" "Struct:" pb __is_only_struct;
    dbg "DECL" "Array:" pb __is_array;
    dbg "DECL" "Static:" pb __is_static;
    dbg "DECL" "With init data:" pb __is_with_init_data;
    dbg "DECL" "lens:" (iterS Exp.pprint ",") lens;
    let elens = (e_eval _s _L) |>>| lens in
    let ilens : int list = term_to_int |>>| elens in
    dbg "DECL" "data:" Block.print_init init_data;
         
    let __x, (ptrs, preds) =
      if __is_with_init_data then
        if __is_only_struct then
          let fields = get_only_fields structs _x in
          if __is_array then
            begin
              pn_s "DECL" "INIT+ARRAY+STRUCT Mode";
              (* let _ns = Exp.get_array_length _x in *)
              dbg "DECL" "Exploring for " Exp.pprint _a_hat;
              _T _a_hat, __alloc_type_struct_init_n init_data __is_static structs _a_hat fields _s _L ilens
            end
          else
            begin
              pn_s "DECL" "INIT+STRUCT Mode(No ARRAY)";
              _T _a_hat, __alloc_type_struct_init init_data __is_static structs _a_hat fields _s _L 1
            end
        else
          if __is_array then
            (* let _ns = Exp.get_array_length _x in *)
            _T _a_hat, __alloc_type_struct_init_n init_data __is_static structs _a_hat [] _s _L ilens
          else
            match init_data with
              Block.INIT_S t ->
              eval _s _L t, ([],[])
            | _ -> raise (StError "Illegal initialized data")
      else
        if __is_only_struct then
          let fields = get_only_fields structs _x in
          if __is_array then
            let _ns = Exp.get_array_length _x in
            _T _a_hat, __alloc_type_struct_n __is_static structs _a_hat fields _s _L ilens
          else
            _T _a_hat, __alloc_type_struct __is_static structs _a_hat fields _s _L 1
        else
          if __is_array then
            let _ns = Exp.get_array_length _x in
            _T _a_hat, __alloc_type_struct_n __is_static structs _a_hat [] _s _L ilens
          else
            if __is_static then
              _T (_C 0), ([],[])
            else
              begin
                pn_s "DECL" "NO (STRUCT+ARRAY+STATIC)";
                _T _a_hat, ([],[])
              end
    in
    let _s' = subs _x __x _s in
    pn_s "DECL" "Subs is done";
    (*
    let res =
      if is_only_struct _x then (**  *)
        begin
          let (ptrs, preds) = alloc_type structs a_hat _x _n in
          let _A' = (fun (a,b,c,d) -> (a,b,c @ ptrs, d @ preds)) _A in
          ([(s',_d,_A',empty,[],_L)])
        end
      else
        if List.length lens > 0 then
          begin
            match data with
              Block.INIT_M ids ->
               let ptrs = List.mapi (fun i d ->
                              match d with
                                Block.INIT_S d' ->
                                 let ptr = Term.op a_hat (Term.EXP (_C i)) Op.ADD in
                                 (ptr, [("*", d')])
                              | _ ->
                                 raise (StError "precond_decl error")
                            ) ids in
               let _A' = (fun (a,b,c,d) -> (a,b,c@ptrs,d)) _A in
               [(s',_d,_A',empty,[],_L)]
            | _ ->
               let a1 = ("Array", [a_hat; offset a_hat _n]) in
               let _A' = (fun (a,b,c,d) -> (a,b,c,a1 :: d)) _A in
               ([(s',_d,_A',empty,[], _L)])
          end
        else
          let a_hat = Term.encode $$ Exp.set_hat (newvar (Exp.get_attributes _x)) in
          let s' = subs _x a_hat _s in
          match data with
            Block.INIT_S tdata ->
            begin
              let p = ASSIGN (_x, tdata, l) in
              fst3 $$ precond (s', _d, _A, _L) packs l_X p
            end
          | _ ->
            ([(s', _d, _A, empty, [], _L)])
    in
    *)

    let _A = (fun (a,b,c,d) -> (a, b, c@ptrs, d@preds)) _A in
    dbg "DECLP" "New cells:\n" (print_post "DECLP" _s' [] ([],[],ptrs,preds) empty) l;
    pn_s "DECLP" "";
    (* List.iter (fun (s,d,a,b,_,_) ->
        print_post "DECL" s d a b l
      ) res; *)
    ([(_s', _d, _A, empty, [], _L)], [], false_d)
  in

  let is_to = tmo "precond" false true in
  if is_to then ([],[],false_d) else
    let (_, _, _, _, _, _) = packs in

    let (res, returns, ds) =
      match _P with
        SKIP l ->
         print_pre "SKIP" _s _d _A l;
         ([(_s, _d, _A, empty, [], _L)], [], false_d)
      | FAIL -> ([],[],(_False, _False, BExp.list_to_bexp _d))
      | LABEL (lbl, el, l) ->
         pn_s "LABEL" lbl;
         print_pre "LABEL" _s _d _A l;
         let _s' = M.filter (fun (k:Exp.t) _ -> (Exp.toStr k) |<- el) _s in
         let _L' = F.add lbl _s' _L in
         ([(_s,_d,_A,empty,[],_L')], [], false_d)
      | ASSIGN (_x, Term.EXP (Exp.ADDR (Exp.ARROW (e_t, _f))), l) ->
         let _t = _T e_t in
         let _st = eval _s _L _t in
         let _v_tld = _T $$ newvar [Exp.INDIRECT; Exp.TILDE] in

         let tr_fields _fields =
           (fun (fields', u) (f,v) ->
             let u', v' = 
               if f=_f then (v, _v_tld) else (u, v)
             in
             (fields' @ [(f,v')] , u')
           ) |->> (([], _T (_C 0)), _fields)
         in
         
         let _X : o list = (** Checked on Jul 9, 2019 *)
           begin
             let _X' = get_ptr _L _s _d _A _t in
             (fun ((_t', _fields),ptrs') ->
               
               let fields', u = tr_fields _fields in
               let cell1 = (_t', fields') in
               let cell2 = (_v_tld, [("*",u)]) in
               let _A'' = (fun (a,b,_,d) -> (a,b,ptrs' @ [cell1;cell2],d)) _A in      
               let _s' = subs _x _v_tld _s in
               let _s_t_eq_t = (eval _s _L _t) == _t' in
               dbg "INDIRECT" "t:" Term.pprint _t;
               dbg "INDIRECT" "s(t)" Term.pprint (eval _s _L _t);
               dbg "INDIRECT" "t':" Term.pprint _t';
               dbg "INDIRECT" "s(t)=t'" BExp.pprint _s_t_eq_t;
               let _d1 = BExp.(_d &&. _s_t_eq_t) in
               let _A' = _PutVarAddr _A'' _x _v_tld in
               (_s', _d1, _A', empty, [], _L)
             ) |>>| _X'
           end
         in
         dbg "INDIRECT" "|X|:" pl (List.length _X);
         let _Y1 = (** Checked on Jul 9, 2019, common for struct and simple pointer type *)
           let _Y1' = get_array_bound _L "Array" _s _d _A _t in
           (fun (_t', _s_t_sub_1, _s_t_add_1, _u, bs, _A') ->
             let (_, _fields') = create_fields _t Exp.TILDE _f packs in
             let fields', u = tr_fields _fields' in
             let _s' = subs _x _v_tld _s in
             let _d' = BExp.evals (_d @ bs) in
             let _subarray1 = ("Array", [_t';_s_t_sub_1]) in
             let _subarray2 = ("Array", [_s_t_add_1;_u]) in
             let _cell = [(eval _s _L _t, fields')] (* [(eval _s _L _t, [(_f, _y_tld)])] *) in
             let subarrays = is_valid_array |>- [_subarray1; _subarray2] in
             let _A'' = (fun (a,b,c,d) -> (a,b, c @ _cell, _A' @ subarrays)) _A in
             let cell2 = (_v_tld, [("*",u)]) in
             let _A' = (fun (a,b,c,d) -> (a,b,c @ [cell2],d)) $$ _PutVarAddr _A'' _x u in
             (_s', _d', _A', empty, [], _L)
           ) |>>| _Y1'
         in
         dbg "INDIRECT" "|Y1|:" pl (List.length _Y1);
         let _Y2 = (** Checked on Jul 9, 2019, only for non-struct type *)
           let _Y2' = extract_list _L _s _d _A _t true in
           let _w_tld = _T $$ newvar [Exp.TILDE] in
           let _x_tld = _T $$ newvar [Exp.TILDE] in
           (fun (s_t, d', (_,u,_), (_,_,ptrs,preds)) ->
             dbg "INDIRECT" "A':" Formula.upprint ([],[],ptrs,preds);
             let (_, fields') = create_fields _t Exp.BAR _f packs in
             if not ("next" |<- (fst |>>| fields')) then (iterS (fun (a,b) -> pw a) "," fields'; raise (StError "(1) next field does not exists.")); 
             let fields = (fun acc (fld_n, value) ->
                 if fld_n = "next" then
                   acc @ [(fld_n, _w_tld)]
                 else if fld_n = _f then
                   acc @ [(fld_n, _v_tld)]
                 else
                   acc @ [(fld_n, value)]
               ) |->> ([], fields') in
             let _s' = subs _x _v_tld _s in
             let _A' = _PutVarAddr ([],[],(s_t, fields)::ptrs, ("List", [_w_tld;u])::preds) _x _x_tld in
             let r = (_s',d',_A',empty,[],_L) in
             r
           ) |>>| _Y2'
         in
         dbg "INDIRECT" "|Y2|:" pl (List.length _Y2);
         let _Y3 = 
           let _Y3' = extract_list _L _s _d _A _t false in
           (fun (s_t, d', (t',u,y_tld),( _,_,ptrs,preds)) ->
             dbg "INDIRECT" "A':" Formula.upprint ([],[],ptrs,preds);
             let (_, fields') = create_fields _t Exp.BAR _f packs in
             let fields = (fun acc (fld_n, value) ->
                 if fld_n = _f then
                   acc @ [(fld_n, _v_tld)]
                 else
                   acc @ [(fld_n, value)]
               ) |->> ([], fields') in
             
             let x_tld = _T $$ newvar [Exp.TILDE] in
             let _s' = subs _x _v_tld _s in
             let _A' = _PutVarAddr ([],[],(s_t, fields)::(_v_tld,[("*",x_tld)])::ptrs, ("List", [t';s_t])::("List", [y_tld; u])::preds) _x x_tld in
             let r = (_s',d',_A',empty,[],_L) in
             r
           ) |>>| _Y3'
         in
         dbg "INDIRECT" "|Y3|:" pl (List.length _Y3);
         
         let res = _X @ _Y1 (* @ _Y2 @ _Y3 *) in
         if List.length res > 0 then p_s "INDIRECT" "X U Y1 U Y2 U Y3: " else pn_s "INDIRECT" "No X U Y{1,2,3}.";
         List.iter (fun (s,d,a,b,_,_) ->
             print_post "INDIRECT" s d a b l
           ) res;
         
         let res2 =
           begin
             let _s_t = eval _s _L _t in
             let _d' = BExp.(_d &&~ not_in_Addr _s_t _A) in
             dbg "INDIRECT" "s(t):" Term.pprint _s_t;
             dbg "INDIRECT" "d & s(t) not in Addr(A):" (iterS BExp.pprint "&") _d';
             if is_bexp_sat _d' then
               begin
                 let (_z_bar, _fields') = create_fields _t Exp.BAR _f packs in
                 let fields', _ = tr_fields _fields' in
                 dbg "INDIRECT" "Newly created cell" Pointer.pprint ((_s_t, fields'));
                 let _s' = subs _x _v_tld _s in

                 let new_cell = (_s_t, fields') in
                 let _A'' = (fun (a,b,c,d) -> (a,b,c @ [new_cell],d)) _A in

                 pn_s "INDIRECT" "SAT";
                 let cell2 = (_v_tld, [("*",_z_bar)]) in
                 let _A' = (fun (a,b,c,d) -> (a,b,c @ [cell2],d)) $$ _PutVarAddr _A'' _x _z_bar in
                 ([_s', _d', _A'', ([],[],[new_cell],[]), [], _L])
               end
             else
               begin
                 pn_s "INDIRECT" "UNSAT";
                 []
               end
           end
         in
         
         if List.length res2 > 0 then p_s "INDIRECT" "Z: " else pn_s "INDIRECT" "No Z1 U Z2.";
         List.iter (fun (s,d,a,b,_,_) ->
             print_post "INDIRECT" s d a b l
           ) res2;
         let _X = res @ res2 in
         dbg "STAT" "INDIRECT:" pl (List.length _X);
         (_X, [], false_d)

      | ASSIGN (_x, _t, l) ->
         p_s "PR" ".";
         dbg "ASSIGN" "ASSIGN t:" Term.pprint _t;

         let t_x = _T _x in
         let s_x : Term.t = (eval _s _L t_x) in (** s(x) *)

         let _t' : Term.t = eval _s _L _t in (** s(t) *)

         let _t_t = (Term.eval _t') in

         let _s' = subs _x _t_t _s in (** This is a temporary trick and not suitable for Java like NULL assignment *)
         let _A' = _PutVarAddr _A _x s_x  in

         let _s'' = sanitize _s' [_t] in

         print_pre "ASSIGN" _s _d _A l;
         pn_s "ASSIGN" ("ASSIGN to " ^ (Exp.toStr _x));
         print_post "ASSIGN" _s' _d _A' empty l;
         dbg "ASSIGN" "After Sanitize:" (print_post "ASSIGN" _s'' _d _A' empty) l;
         
         ([(_s'', _d, _A', empty, [], _L)], [], false_d)
      | IF (_b, _P1, _P2, l) ->
         p_s "PR" "|";
         print_pre "IF" _s _d _A l;

         dbg "IF" "b:" BExp.pprint _b;
         let s_b  = eval_b _L _s _b in                     (** s(b) *)
         dbg "IF" "s(b):" BExp.pprint s_b;
         let s_nb = BExp.complement s_b in   (** not s(b) *)

         let res =
           begin
             let _b1 = s_b in
             let _b2 = s_nb in
             let d1 = BExp.evals (_d @@ [_b1]) in
             let d2 = BExp.evals (_d @@ [_b2]) in

             dbg "IF" "d & b:" (iterS BExp.pprint " && ") d1;
             dbg "IF" "d & (not b):" (iterS BExp.pprint " && ") d2;

             let b1_sat = is_bexp_sat d1 in
             let b2_sat = is_bexp_sat d2 in

             if b1_sat && b2_sat then
               (
                 pn_s "IF" "both b and not b are sat";
                 dbg "IF" "SAT: b:\n" BExp.pprint _b1;
                 (* dbg "IF" "_P1 is :" pprint _P1; *)
                 let (_X1, _X2, _) = tmo "if" (precond (_s, d1, _A, _L) packs l_X _P1) [] in
                 dbg "IF" "SAT: (not b):\n" BExp.pprint _b2;
                 let (_Y1, _Y2, _) = tmo "if" (precond (_s, d2, _A, _L) packs l_X _P2) [] in
                 (* dbg "COMPLEXITY" "" BExp.pprint (_b);
                 pn_s "COMPLEXITY" ("Going to join: X1 " ^ (string_of_int (List.length _X1)) ^ " and Y1 " ^ ((string_of_int (List.length _Y1))) ); *)
                 let r1 = _join _X1 _Y1 in
                 dbg "COMPLEXITY" "Number of Returned Branches:" pl (List.length r1);
                 (r1, _retjoin _X2 _Y2, false_d)
               )
             else if b1_sat && not b2_sat then
               (
                 dbg "IF" "SAT (b):\n" BExp.pprint _b1;
                 tmo "if" (precond (_s, d1, _A, _L) packs l_X _P1) []
               )
             else if not b1_sat && b2_sat then
               (
                 dbg "IF" "SAT (not b):\n" BExp.pprint _b2;
                 tmo "if" (precond (_s, d2, _A, _L) packs l_X _P2) []
               )
             else
               (
                 pn_s "IF" "b1 and not b1 both are unsat";
                 ([], [], false_d)
               )
           end
         in
         dbg "GC" "Program Started\n" print_gc $$ Gc.stat ();
         print_them "IFS" (fst3 res) _P;
         pause "Press any key to continue";
         res
      | COMP (_P1, _P2', l) ->
         let (res1, (_X : (Term.t * Term.t M.t * BExp.t list * Formula.ut * Formula.ut) list), (d_1,d_2,d_3)) = tmo "comp" (precond (_s, _d, _A, _L) packs l_X _P1) [] in
         
         (*if List.length res1 > 8 then
           begin *)
           
         dbg "LINE" "" pn (Locs.to_str l);
         dbg "COMP" "Current Line:" pprint _P1;
         (* dbg "COMP" "Rest Program:\n----------\n" pprint _P2'; *)
         pn_s "COMP" "----------\n";
         print_pre "COMP" _s _d _A l;

         if List.length res1 > 0 then p_s "COMP" "res1: ";
         List.iter (fun (s,d,a,b,_,_) ->
             print_post "COMP" s d a b l
           ) res1;

         if List.length _X > 0 then p_s "COMP" "_X:";
         List.iter (fun (u,s,d,a,b) ->
             print_post "COMP" s d a b l
           ) _X;

         let _P2 =
           match _P1 with
             DECL (v, _, Block.INIT_E, _)
           | DECL (v, _, Block.INIT_S _, _) ->
              if Exp.is_struct v && not (Exp.is_ptr v) then
                begin
                  let _P2 = star_substitute v (Term.EXP (Exp.REF v)) _P2' in
                  dbg "AMP" "New P2:\n" pprint _P2;
                  _P2
                end
              else
                _P2'
           | _ -> _P2'
         in

         pn_s "COMP" "P2 is recomputed\n";

         let res_all = (fun ((s,d,a,b1,v1,_L) as _Ii:o) ->
             let packs' = (fun (a1,a,b,c,d,e) -> (a1,a,b,c,d,e)) packs in
             pn_s "COMP" "P2 is going to be called\n";
             let (_J, (_Yk : (Term.t * Term.t M.t * BExp.t list * Formula.ut * Formula.ut) list), ds') = precond (s,d,a,_L) packs' l_X _P2 in
             dbg "COMP" "Postcond from P1:" (fun ((a,b,c,d,_,_):o) -> print_post "COMP" a b c d l) _Ii;
             dbg "COMP" "Postcond from P2:" (iterS (fun (a,b,c,d,_,_) -> print_post "COMP" a b c d l) "\n") _J;
             
             let _Ii_Ij : (o * o) list = (fun _j -> (_Ii,_j)) |>>| _J in
             let _Ii_Yk = (fun _Y -> (_Ii,_Y)) |>>| _Yk in
             ((_Ii_Ij, _Ii_Yk), ds')
           ) |>>| res1 in

         dbg "COMP" "Current Line (2nd Phase):" pprint _P1;
         let (res, d_res) = List.split res_all in

         let (_Ii_Ij', _Ii_Yk') = List.split res in
         
         let _Ii_Ij = concat _Ii_Ij' in
         
         let _Ii_Yk = concat _Ii_Yk' in
         dbg "COMP" "|J|:" pl (List.length _Ii_Ij);
         dbg "COMP" "|K|:" pl (List.length _Ii_Yk);
         let (d1s, d2s, d3s) =
           if List.length d_res = 0 then
             false_d
           else
             (fun (d1,d2,d3) (d1',d2',d3') -> (d1 |. d1', d2 |. d2', d3 |. d3')) |->> ((d_1,d_2,d_3), d_res) in

         let join_formula b' (a3,b3,c3,d3) =
           let b1 = Formula.(b' *~~ c3) in
           let b2 = Formula.(b1 #~~ d3) in
           b2
         in

         let is_unsat_j, _or_d_l_j, _I0 = (fun (flag, _or_d_l, acc) ((_,_,_,_Bi,_,_), (sij,dij,_Aij,_Bij,vij,_Lij)) ->
             dbg "COMP" "Aij:" Formula.upprint _Aij;
             dbg "COMP" "Bi:" Formula.upprint _Bi;
             dbg "COMP" "Bij:" Formula.upprint _Bij;
             let b = join_formula _Bi _Bij in
             dbg "COMP" "Bi*Bij (b):" Formula.upprint b;
             
             let a = join_formula _A $$ b in
             dbg "COMP" "A*Bi*Bij:" Formula.upprint a;
             
             let pure_a = _pure a in
             let dij_purea = dij @ pure_a in
             
             dbg "COMP" "dij & Pure(A*Bi*Bij):" (iterS BExp.pprint " & ") dij_purea;

             let is_sat = is_bexp_sat (dij @ pure_a) in
             dbg "COMP" "Is Sat:" pb is_sat;
             
             if is_sat then
               flag, _or_d_l, (* _join *) acc @@ [(sij, dij, _Aij, b, vij, _Lij)]
             else
               let _and_d = BExp.list_to_bexp dij in
               true, _or_d_l @ [_and_d], acc
           ) |->> ((false, [], []), _Ii_Ij) in

         let is_unsat_k, _or_d_l_k, _I1 = (fun (flag, _or_d_l, acc) ((_,_,_,_Bi,_,_), (rij,sij,dij,_Aij,_Bij)) ->
             dbg "COMP" "Bi:" Formula.upprint _Bi;
             dbg "COMP" "Bij:" Formula.upprint _Bij;
             let b = join_formula _Bi _Bij in
             dbg "COMP" "Bi*Bij:" Formula.upprint b;

             let a = join_formula _A $$ b in
             dbg "COMP" "A*Bi*Bij:" Formula.upprint a;

             let pure_a = _pure a in
             if is_bexp_sat (dij @ pure_a) then
               flag, _or_d_l, acc @ [(rij, sij, dij, _Aij, b)]
             else
               let _and_d = BExp.list_to_bexp dij in
               true, _or_d_l @ [_and_d], acc
           ) |->> ((false, [], []), _Ii_Yk) in

         let t1 = if is_unsat_j then
                    begin
                      let dd = list_to_disj _or_d_l_j in
                      d1s |. dd
                    end
                  else d1s in
         let t2 = if is_unsat_k then t1 |. (list_to_disj _or_d_l_k) else t1 in

         let _I2 = (* _retjoin *) _X @@ _I1 in
         dbg "COMP" "|I0|:" pl (List.length _I0);
         dbg "COMP" "|X@I1|:" pl (List.length _I2);
         (*
         if List.length _I0 > 32 then
           begin
             dbg "COMPLEXITY" "Current Line:" pprint _P1;
             dbg "COMPLEXITY" "From P1*P2: " pl (List.length _I0);
             pn "Enter";
             let _ = read_line () in
             ()
           end;
          *)

         List.iter (fun (s,d,a,b,_,_) ->
             print_post "COMP" s d a b l
           ) _I0;

         
         (_I0, _I2, (t2, d2s, d3s))

      | MALLOC (_x, exp, l) ->
         let rec contain_sizeof = function
             Exp.SIZEOF _ -> true
           | Exp.BINOP (e1,_,e2) -> contain_sizeof e1 || contain_sizeof e2
           | _ -> false
         in

         let exp' = e_eval _s _L exp in
         dbg "UNFOLD" "exp':" Term.pprint exp';
         let _tau, _t =
           match exp' with
             Term.EXP (Exp.SIZEOF (_tau)) ->
              pn (_tau ^ " ...................................");
              _tau, Exp.CONST 1
           | Term.EXP (Exp.BINOP (Exp.SIZEOF (_t), Op.MUL, _len))
             | Term.EXP (Exp.BINOP (_len, Op.MUL, Exp.SIZEOF (_t))) -> _t, _len
           | Term.EXP e when not (contain_sizeof e) && not (Exp.is_struct _x) ->
              Exp.size_to_type $$ Exp.size_of _x, e
           | Term.NULL ->
              raise (StError "(Totally) Unexpected malloc case")
           | Term.EXP e ->

              dbg "UNFOLD" "MALLOC ERROR" (print_pre "UNFOLD" _s _d _A) l;
              pw "In function: "; pn !current_function;
              pw "exp: "; Exp.pprint exp; pn "";
              pw "Eval(exp): "; Term.pprint exp'; pn "";
              pw "Is struct:"; pb (Exp.is_struct _x); pn "";
              pw "Is struct:"; pb (contain_sizeof e); pn "";
              raise (StError "Unhandled malloc case")
              (* if Exp.is_struct _x then
                let _tau = Exp.get_struct_name _x in
                let size_t = Exp._struct_size_by_name structs _tau in
                let _t = Exp.eval ~structs:structs (Exp.BINOP (exp, Op.DIV, Exp.CONST size_t)) in
                _tau, _t
              else
                let _tau' = Exp.type_of_var (Exp.get_attributes _x) in
                match _tau' with
                  Exp.SIZEOF _tau ->
                   let size_t = Exp.simple_size _tau in
                   let _t = Exp.eval (Exp.BINOP (exp, Op.DIV, Exp.CONST size_t)) in
                   _tau, _t
                | _ -> raise (StError "Strang simple type") *)
         in
         begin
           let _st = eval _s _L (_T _t) in
           dbg "MALLOC" "_s(t):" Term.pprint _st;
           let is_fail =
             if (Exp.is_struct _x) then
               match _st with
                 Term.EXP (Exp.CONST _) -> false
               | _ -> true
             else
               false
           in
           dbg "MALLOC" "is_fail:" pb is_fail;
           if not is_fail then
             begin
               let _st_n0 = _st =/ Term.EXP (Exp.CONST 0) in (* s(t)/=0 *)
               dbg "MALLOC" "s(t)=/0:" BExp.pprint _st_n0;
               let _d_st_n0 = _d @@ [_st_n0] in
               dbg "MALLOC" "d & s(t)=/0:" (iterS BExp.pprint " & ") _d_st_n0;
               let _d_st_n0_sat_res = is_bexp_sat _d_st_n0 in
               dbg "MALLOC" "sat_res:" pb _d_st_n0_sat_res;

               let _xt = _T _x in
               let _st_0 = _st == Term.EXP (Exp.CONST 0) in (* s(t)/=0 *)
               dbg "MALLOC" "s(t)=0:" BExp.pprint _st_0;
               let _d_st_0 = _d @@ [_st_0] in
               let _d_st_0_sat_res = is_bexp_sat _d_st_0 in
               dbg "MALLOC" "sat_res:" pb _d_st_0_sat_res;

               let _X =
                 if _d_st_n0_sat_res then
                   begin
                     let x_hat   = Exp.add_attr Exp.GLOBAL (Exp.set_hat (newvar (Exp.get_attributes _x))) in (** ^x *)
                     let x_acute = Exp.add_attr Exp.GLOBAL (Exp.set_acute (newvar (Exp.get_attributes _x))) in
                     dbg "MALLOC" "d & s(t)=/0 & Pure(A):" Exp.pprint x_acute;
                     let _s1 = subs _x (_T x_acute) _s in (* s[x:=^x] *)
               
                     let x_hatT : Term.t = _T x_hat in
                     let x_acuteT : Term.t = _T x_acute in
                     let _d1' = BExp.(_d_st_n0 &&. (x_hatT == x_acuteT)) in
                     let (_, _, _, _, (structs : Structure.t V.t), _) = packs in
                     let fields = get_only_fields2 structs _tau in (** _x substituted by _tau *)
                     dbg "MALLOC" "fields:" (iterS Exp.pprint "&" ) fields;
                     
                     
                     let (alloc_ptr, alloc_pred) =
                       if Exp.is_struct _x then
                         begin
                           let _st_I = Term.get_int l _st in
                           dbg "MALLOC" "ist:" pl _st_I;
                           __alloc_type_struct false structs x_hat fields _s _L _st_I
                         end
                       else
                         __alloc_type_sigma x_hatT _s _L _st
                     in
                     (* alloc_type structs x_hat _x _st in *)
                     
                     let alloc_ptr' = Pointer.substitute (_T x_hat) (_T x_acute) |>>| alloc_ptr in
                     let alloc_pred' = Predicate.substitute (_T x_hat) (_T x_acute) |>>| alloc_pred in
                     let _d1 = _d1' @ _pure ([], [], alloc_ptr', alloc_pred') in
                     dbg "MALLOC" "_d1:" (iterS BExp.pprint "&" ) _d1;

                     let size_cell_ptr = Term.size_loc @+@ x_hatT in
                     let size = _T ((Exp.__size_by_name V.empty structs _tau)) @*@ _st in
                     let size_cell = (size_cell_ptr, [("*", size)]) in
                     let _A2 = (fun (a,b,c,d) -> (a,b,c @ alloc_ptr @ [size_cell],d @ alloc_pred)) _A in
                     let _A1 = _PutVarAddr _A2 _x x_hatT in
                     
                     let res1 = (_s1, BExp.evals _d1, _A1, empty, [], _L) in
                     dbg "MALLOC" "New s(X1):" (m_print "MALLOC") _s1;
                     dbg "MALLOC" "New A(X1):" Formula.pprint [_A1];

                     let x_acute_eq_null = x_acuteT == Term.NULL in
                     let res2 = (_s1, _d @ [_st_n0; x_acute_eq_null], _PutVarAddr _A _x x_acuteT, empty, [], _L) in
                     [res1; res2]
                       (* cdc... e.coli... *)
                   end
                 else
                   let _st_0 = _st == Term.EXP (Exp.CONST 0) in
                   [(_s,_d @ [_st_0] ,_A,empty,[],_L)]
               in
               dbg "MALLOC" "MALLOC:" pl (List.length _X);
               iterS (fun x -> pprint_f "MALLOC" x l) "\n" _X ; pn "";
               (_X, [], false_d)
             end
           else
             raise (PrecondFails "MALLOC contains NON-Constant length")
         end
      | SARRAY (_x, _t, _, l) ->
         p_s "PR" "+";
         let _a_hat = _T (newvar (Exp.get_attributes _x)) in
         let _s' = subs _x _a_hat _s in (** s[x:=^a] *)
         let _Array = ("Array", [_a_hat; Term.op _a_hat (Term.op _t (Term.EXP (_C 1)) Op.SUB) Op.ADD]) in
         let _A' = (fun (ex, pure, ptr, pred) -> (ex, pure, ptr, pred @ [_Array])) _A in
         ([(_s', _d, _A', empty, [], _L)], [], false_d)
      | LOOKUP (_x, _t, _f, l) ->
         p_s "PR" "^";
         (** Cell *)
         let _st = eval _s _L _t in
         begin
           match _f, _st with
             "*", Term.EXP (Exp.ADDR (e)) ->
              let _P' = ASSIGN (_x, Term.EXP e, l) in
              tmo "if" (precond (_s, _d, _A, _L) packs l_X _P') []
           | _ ->
              dbg "LOOKUP" "(Lookup) state:\n" (print_pre "LOOKUP" _s _d _A) l;
              dbg "LOOKUP" "x:" Exp.pprint _x;
              dbg "LOOKUP" "t:" Term.pprint _t;

              let _X : o list = (** Checked on Jul 9, 2019 *)
                begin
                  let _X' = get_ptr _L _s _d _A _t in
                  (fun ((_t', _fields),ptrs') ->
                    let _u, _A'' =
                      try
                        let u = try snd (List.find (fun (fn, _) -> fn = _f) _fields) with _ -> raise (StError "LOOKUP: wrong field name") in
                        u, _A
                      with
                        _ ->
                        let t__attr = try Exp.get_attributes $$ Term.head ((Term.toStr _t)) _t with _ -> Exp.get_attributes _x in
                        let _z_bar = _T (Exp.set_bar (newvar t__attr))
                        in
                        let _A' = (fun (a,b,c,d) -> (a,b,ptrs' @ [(_t', _fields@[(_f, _z_bar)])],d)) _A in
                        (_z_bar, _A') (** added by me for uninitialized field *)
                    in
                    let _s' = subs _x (eval _s _L _u) _s in
                    let _s_t_eq_t = (eval _s _L _t) == _t' in
                    dbg "LOOKUP" "t:" Term.pprint _t;
                    dbg "LOOKUP" "s(t)" Term.pprint (eval _s _L _t);
                    dbg "LOOKUP" "t':" Term.pprint _t';
                    dbg "LOOKUP" "s(t)=t'" BExp.pprint _s_t_eq_t;
                    let _d1 = BExp.evals (_d @ [_s_t_eq_t]) in
                    let _A' = _PutVarAddr _A'' _x _u in
                    (_s', _d1, _A', empty, [], _L)
                  ) |>>| _X'
                end
              in
              dbg "LOOKUP" "|X|:" pl (List.length _X);
              let _Y1 = (** Checked on Jul 9, 2019, common for struct and simple pointer type *)
                let _Y1' = get_array_bound _L "Array" _s _d _A _t in
                (fun (_t', _s_t_sub_1, _s_t_add_1, _u, bs, _A') ->
                  let (_y_tld, fields') = create_fields _t Exp.TILDE _f packs in
                  let _s' = subs _x _y_tld _s in
                  let _d' = BExp.evals (_d @ bs) in
                  let _subarray1 = ("Array", [_t';_s_t_sub_1]) in
                  let _subarray2 = ("Array", [_s_t_add_1;_u]) in
                  let _cell = [(eval _s _L _t, fields')] (* [(eval _s _L _t, [(_f, _y_tld)])] *) in
                  let subarrays = is_valid_array |>- [_subarray1; _subarray2] in
                  let _A'' = (fun (a,b,c,d) -> (a,b, c @ _cell, _A' @ subarrays)) _A in
                  let _A' = _PutVarAddr _A'' _x _y_tld in
                  (_s', _d', _A', empty, [], _L)
                ) |>>| _Y1'
              in
              dbg "LOOKUP" "|Y1|:" pl (List.length _Y1);
              let _Y2 = 
                let _Y2' = get_array_bound _L "Stringpart" _s _d _A _t in
                (fun (_t', _s_t_sub_1, _s_t_add_1, _u, bs, _) ->
                  let _y_tld = _T (Exp.set_tilde (newvar [])) in
                  let _s' = subs _x _y_tld _s in
                  let _d' = BExp.evals (_d @ bs) in
                  let _letter_y_tld = [_Letter _y_tld] in
                  let _substr1 = ("Stringpart", [_t';_s_t_sub_1]) in
                  let _substr2 = ("Stringpart", [_s_t_add_1; Term.op _u (Term.EXP (_C 1)) Op.SUB]) in
                  let substrs = is_valid_array |>- [_substr1; _substr2] in
                  let _cell = [(eval _s _L _t, [(_f, _y_tld)])] in
                  let _A'' = (fun (a,b,c,d) -> (a,b @ _letter_y_tld, c @ _cell, d @ substrs)) _A in
                  let _A' = _PutVarAddr _A'' _x  _y_tld in
                  (_s', _d', _A', empty, [], _L)
                ) |>>| _Y2'
              in
              dbg "LOOKUP" "|Y2|:" pl (List.length _Y2);
              
              let _Y3 = if (_f = "*") then [] else
                          let _Y3' = extract_list _L _s _d _A _t true in
                          (fun (s_t, d', (_t',u,_), (_,_,ptrs,preds)) ->
                            dbg "LOOKUP" "A':" Formula.upprint ([],[],ptrs,preds);
                            let (_, fields') = create_fields _t Exp.BAR _f packs in
                            if not ("next" |<- (fst |>>| fields')) then (iterS (fun (a,b) -> pw a) "," fields'; raise (StError "(2) next field does not exists."));  
                            let (_, v_tld) = List.find (fun (fn,_) -> fn = "next") fields' in
                            let (_, x_tld) = List.find (fun (fn,_) -> fn = _f) fields' in
                            let _s' = subs _x x_tld _s in
                            let _A' = _PutVarAddr ([],[],(_t', fields')::ptrs, ("List", [v_tld;u])::preds) _x x_tld in
                            let r = (_s',d',_A',empty,[],_L) in
                            r
                          ) |>>| _Y3'
              in
              dbg "LOOKUP" "|Y3|:" pl (List.length _Y3);

              let res = sat_A (_X @ _Y1 @ _Y2 @ _Y3) (* @ _Y4 *) in
              if List.length res > 0 then p_s "LOOKUP" "X U Y1 U Y2 U Y3: " else pn_s "LOOKUP" "No X U Y{1,2,3}.";
              List.iter (fun (s,d,a,b,_,_) ->
                  print_post "LOOKUP" s d a b l
                ) res;
              
              let res2' =
                begin
                  let _s_t = eval _s _L _t in
                  let _s_t_not_in_Addr_A = not_in_Addr _s_t _A in
                  dbg "LOOKUP" "s(t) not in Addr(A):" (iterS BExp.pprint "&") _s_t_not_in_Addr_A;
                  dbg "LOOKUP" "d:" (iterS BExp.pprint "&") _d;
                  let _d' = BExp.(_d &&~ _s_t_not_in_Addr_A) in
                  dbg "LOOKUP" "s(t):" Term.pprint _s_t;
                  dbg "LOOKUP" "d & s(t) not in Addr(A):" (iterS BExp.pprint "&") _d';
                  if is_bexp_sat _d' then
                    begin
                      let (_z_bar, fields') = create_fields _t Exp.BAR _f packs in
                      dbg "LOOKUP" "Newly created cell" Pointer.pprint ((_z_bar, fields'));
                      let _s' = subs _x _z_bar _s in

                      let new_cell = (eval _s _L _t, fields') in
                      let _A'' = (fun (a,b,c,d) -> (a,b,c @ [new_cell],d)) _A in
                      pn_s "LOOKUP" "SAT";
                      ([_s', _d', _PutVarAddr _A'' _x _z_bar, ([],[],[new_cell],[]), [], _L])
                    end
                  else
                    begin
                      pn_s "LOOKUP" "UNSAT";
                      []
                    end
                end
              in

              let res2 = sat_A res2' in

              if List.length res2 > 0 then p_s "LOOKUP" "Z: " else pn_s "LOOKUP" "No Z1 U Z2.";
              List.iter (fun (s,d,a,b,_,_) ->
                  print_post "LOOKUP" s d a b l
                ) res2;
              let _X = (res @ res2) in
              dbg "STAT" "LOOKUP:" pl (List.length _X);
              (_X, [], false_d)
         end
      | MUTATION (_t, _f, _u, l) ->
         p_s "PR" "^";
         let _s_t = eval _s _L _t in
         let _s_u = eval _s _L _u in
         dbg "MUTATION" "t:" Term.pprint _t;
         dbg "MUTATION" "s(t):" Term.pprint _s_t;
         begin
           match _f, _s_t with
             "*", Term.EXP (Exp.ADDR (Exp.VAR _ as y)) ->
              let _P' = ASSIGN (y, _u, l) in
              tmo "if" (precond (_s, _d, _A, _L) packs l_X _P') []
           | _ ->
              let _u = eval _s _L _u in
              let _X : o list =
                let _X' = get_ptr _L _s _d _A _t in
                (fun ((_t', _fields),  _ptrs') ->
                  let fns = fst |>>| _fields in
                  let (_fields': (Field.t * Term.t) list) =
                    if _f |<- fns then
                      (fun (fn, v) -> if fn=_f then (fn, _s_u) else (fn,v)) |>>| _fields
                    else
                      (_f, _s_u)::_fields
                  in
                  let (_A': Formula.ut) = (fun (a,b,c,d) -> (a,b,(_t', _fields')::_ptrs',d)) _A in
                  let _s_t_eq_t = (eval _s _L _t) == _t' in
                  let _A'' = (fun (a,b,c,d) -> (a,b,c,d)) _A' in
                  dbg "MUTATION" "s(t)=t" BExp.pprint _s_t_eq_t;
                  let _d1 = BExp.evals (_d @ [_s_t_eq_t]) in
                  (_s, _d1, _A'', empty, [], _L)
                ) |>>| _X'
              in

              let get_fields () =
                let (_, fields') = create_fields _t Exp.BAR _f packs in
                let fields = (fun (fn,value) -> if fn = _f then (fn,_s_u) else (fn, value)) |>>| fields' in
                fields
              in
              
              let _Y1 =
                let _Y1' = get_array_bound _L "Array" _s _d _A _t in
                (fun (_t', _s_t_sub_1, _s_t_add_1, _u', bs, preds) ->
                  let _d' = BExp.evals (_d @ bs) in
                  let _subarray1 = ("Array", [_t';_s_t_sub_1]) in
                  let _subarray2 = ("Array", [_s_t_add_1;_u']) in
                  let subarrays = is_valid_array |>- [_subarray1; _subarray2] in
                  let _cell = [(eval _s _L _t, get_fields ())] in
                  let _A' = (fun (a,b,c,d) -> (a,b, c @ _cell, preds @ subarrays)) _A in
                  (_s, _d', _A', empty, [], _L)
                ) |>>| _Y1'
              in
              let _Y2 =
                let _Y2' = get_array_bound _L "Stringpart" _s _d _A _t in
                (fun (_t', _s_t_sub_1, _s_t_add_1, _u, bs, unmatched) ->
                  let _d' = BExp.evals (_d @ bs) in
                  let _substr1 = ("Stringpart", [_t';_s_t_sub_1]) in
                  let _substr2 = ("Stringpart", [_s_t_add_1; Term.op _u (Term.EXP (_C 1)) Op.SUB]) in
                  let substrs = is_valid_array |>- [_substr1; _substr2] in
                  let _cell = [(eval _s _L _t, [(_f, _u)])] in
                  let _last_cell = [(_u, [("*", Term.zero)])] in
                  let _A' = (fun (a,b,c,d) -> (a,b, c @ _cell @ _last_cell, d @ substrs)) _A in
                  (_s, _d', _A', empty, [], _L)
                ) |>>| _Y2'
              in

              let _Y3 = if _f = "*" then [] else
                          let _Y3' = extract_list _L _s _d _A _t true in
                          (fun (s_t, d', (_,u',_), (_,_,ptrs,preds)) ->
                            dbg "MUTATION" "A':" Formula.upprint ([],[],ptrs,preds);
                            let fields = get_fields () in
                            if not ("next" |<- (fst |>>| fields)) then raise (StError "next field does not exists.");
                            
                            let (_, v_tld) = List.find (fun (fn,_) -> fn = "next") fields in
                            
                            let _A' = ([],[],(s_t, fields)::ptrs, ("List", [v_tld;u'])::preds) in
                            let r = (_s,d',_A',empty,[],_L) in
                            r
                          ) |>>| _Y3'
              in
              dbg "MUTATION" "|X|:" pl (List.length _X);
              dbg "MUTATION" "|Y1|:" pl (List.length _Y1);
              dbg "MUTATION" "|Y2|:" pl (List.length _Y2);
              dbg "MUTATION" "|Y3|:" pl (List.length _Y3);
              
              let res = _X @ _Y1 @ _Y2 @ _Y3 in
              if List.length res > 0 then p_s "MUTATION" "X U Y: " else pn_s "MUTATION" "No X U Y.";
              List.iter (fun (s,d,a,b,_,_) ->
                  print_post "MUTATION" s d a b l
                ) res;
              
              let res2 =
                let _s_u = eval _s  _L _u in
                let _d' = BExp.evals (_d @ not_in_Addr _s_t _A) in
                let to_check =  ([], not_in_Addr _s_t _A @ _d', [], []) in
                begin
                  let cell = (_s_t, [(_f, _s_u)]) in
                  let _A' = (fun (a,b,c,d) -> (a,b,c @ [cell],d)) _A in
                  let _tau = [] in
                  let vt = Term.head "MUTATION(Z)" _t in
                  if Exp.is_struct vt && not (Exp.is_ptrptr vt && _f="*")  then
                    begin
                      let (_, _, _, _, (structs : Structure.t V.t), _) = packs in
                      let tau = Exp.get_struct_name (Term.toExp _t) in
                      let fields_attr = try ((fun (_,x,_)->x) (V.find tau structs)) with _ -> raise (StError "MUTATION") in
                      let fields = fst |>>| fields_attr in
                      let _fields = __N |>>| fields in
                      let t__attr =
                        try
                          Exp.get_attributes $$ Term.head (Term.toStr _t) _t
                        with _ ->
                          try
                            snd (__V (List.find (fun f' -> __N f' = _f) fields))
                          with
                            _ -> []
                      in
                      let fields' = (fun fld ->   (** @Jul29 *)
                          if _f=fld then
                            (_f, _s_u)
                          else
                            let z_tilde = _T (Exp.set_tilde (newvar t__attr)) in
                            (fld, z_tilde)) |>>| _fields in
                      let m_fields = (fun fld ->
                          let z_tilde = _T (Exp.set_tilde (newvar t__attr)) in
                          (fld, z_tilde)) |>>|  _fields in
                      let cell = (_s_t, fields') in
                      let mcell = (_s_t, m_fields) in
                      let _A' = (fun (a,b,c,d) -> (a,b,c @ [cell],d)) _A in
                      let missing = ([mcell],[]) in
                      let _B' = (fun (c',d') -> ([],[],c',d')) missing in
                      if VcpVBase.check_sat2 to_check then
                        [(_s,_d',_A',_B',[], _L)]
                      else
                        []
                    end
                  else
                    begin
                      let missing = ("Array", [_s_t;_s_t]) in
                      let _B' = ([],[],[],[missing]) in
                      if VcpVBase.check_sat2 to_check then
                        [(_s,_d',_A',_B',[], _L)]
                      else
                        []
                    end
                end
              in
              let res2' =
                (fun (_s,_d,_A,_B,_,_) ->
                  let _s' = sanitize _s [_t] in
                  (_s',_d,_A,_B,[],_L)
                ) |>>| (res @ res2) in
              if List.length res2 > 0 then p_s "MUTATION" "Z1 U Z2: " else pn_s "MUTATION" "No Z1 U Z2.";
              List.iter (fun (s,d,a,b,_,_) ->
                  print_post "MUTATION" s d a b l
                ) res2;
              dbg "STAT" "MUTATION:" pl (List.length res2);
              (res2', [], false_d)
         end
      | DISPOSE (_t, l) ->
         p_s "PR" "-";
         print_pre "DISPOSE" _s _d _A l;
         let _s_t = eval _s _L _t in
         let size_cell_ptr = Term.size_loc @+@ _s_t  in
         let t__attr = try Exp.get_attributes $$ Term.head (Term.toStr _t) _t with _ -> [] in
         let n_tilde = _T $$ Exp.set_tilde (newvar t__attr) in
         let size_cell = (size_cell_ptr, [("*", n_tilde)]) in
         let array = ("Array", [_s_t; _s_t @+@ n_tilde @-@ _T (_C 1)]) in

         let getX () =
           let leftF = _A in (* conj_d_A _d _A in *) (** @Jul29 *)
           let rightF = ([],[],[size_cell],[array]) in
           pn_s "DISPOSE" "Bi-abduction Report: biabd(";
           pf_s "DISPOSE" Formula.pprint [leftF]; p_s "DISPOSE" " * Xi |- Yi * ";
           pf_s "DISPOSE" Formula.pprint [rightF]; pn_s "DISPOSE" ")";

           let (res, d_2) = VcpVBase.biabd leftF rightF in
           dbg "DISPOSE" "Number of biabd brances:" pi (List.length res);
           let res2=
             (fun acc (((_, _d', _Xptrs, _Xpreds) as _X), _Y) ->
               p_s "DISPOSE" "\nXi: ";
               pf_s "DISPOSE" Formula.pprint [_X]; p_s "DISPOSE" "    ";
               p_s "DISPOSE" "Yi: ";
               pf_s "DISPOSE" Formula.pprint [_Y]; pn_s "DISPOSE" "\n";

               let to_check = _d' @ _pure _Y in
               if is_bexp_sat to_check then
                 let _d1 = BExp.evals (_d @ _d') in
                 acc @ [(_s, _d1, _Y, ([],[],_Xptrs, _Xpreds), [], _L)]
               else
                 acc
             ) |->> ([], res) in
           res2, BExp.list_to_bexp d_2
         in

         let _X, d_2 = getX () in
         List.iter (fun (s,d,a,b,_,_) ->
             print_post "DISPOSE" s d a b l
           ) _X;
         dbg "STAT" "DISPOSE:" pl (List.length _X);
         (_X, [], (_False, d_2, _False))
      | PROCCALL (f_name, args, l) ->
         p_s "PR" "<"; p_s "PR" f_name; p_s "PR" ">";
         dbg "BIABD" ("PROCCALL started: " ^ f_name ^ "\n") (print_pre "BIABD" _s _d _A) l;

         dbg "GLO" (f_name ^ "@0:") (m_print "GLO") _s;
         dot ();
         let ret attr = __E ("$ret", attr) in
         let this, (analyzed_functions : fs), currents, (globals : Exp.t list), structs, all_functions = packs in
         
         let compute_proccall is_analyzed attr params specs (d_1,d_2,d_3) =

           (** param-arg pair list: [(p1,a1);(p2,a2);...] *)
           let min_len = if List.length params < List.length args then List.length params else List.length args in
           let rec take n a =
             match n, a with
               _, [] -> []
             | 0, _ -> []
             | n, x::xs -> x::(take (n-1) xs)
           in
           let params_args = List.combine (take min_len params) (take min_len args) in
                 
           if not is_analyzed then
             begin
               pn_s "BIABD" "Not analyzed before.";
               let pas = (fun pas (p,a) ->
                   let a' =
                     match a with
                       Term.EXP (Exp.ADDR (Exp.VAR v)) ->
                        let a' = VcpVBase.qvar () in
                        a'
                     | _ ->
                        eval _s _L a
                           in
                           pas@[a']
                 ) |->> ([], params_args) in
               
               let u = Term.EXP (Exp.FCALL (f_name, Term.toExp |>>| pas)) in
               let out = (subs (ret []) u _s,_d,_MakeArray _A,empty,[],_L) in
               ([out], [], false_d)
             end
           else
             (** sL is the part of _s where variables are not global that is local and parameter *)
             let sL = M.filter (fun key _ -> not (Exp.is_global key)) _s in
             dbg "BIABD" "global vars:" (iterS Exp.pprint ",") globals;
                   
             (** Some function definitions *)
             (** bexp[g- := _s(g)] for all g in globals *)
             (** substitute is BExp.substitute *)
             let prime_nonL substitute data =
               (** First global susbstitution *)
               let data' = (fun bexp gvar ->
                   let gvar_bar = Exp.set_bar gvar in
                   try
                     substitute (_T gvar_bar) (M.find gvar _s) bexp
                   with
                     Not_found ->
                     bexp
                 ) |->> (data, globals) in
                       (** Then param substitution *)
               (fun bexp (param, arg) ->
                 let v_param = Term.toExp param in
                 let param_bar = _T (Exp.set_bar v_param) in
                 match arg with
                   Term.EXP (Exp.ADDR _) ->
                    substitute param_bar (_T (_C 100)) bexp
                 | _ ->
                    substitute param_bar (eval _s _L arg) bexp) |->> (data', params_args)
             in
                   
             (** substitute is Formula.usubstitute *)
             let prime_L substitute bexp =
               let bexp' = (fun bexp gvar ->
                   try
                     let gvar_bar = Exp.set_bar gvar in
                     substitute (_T gvar_bar) (try M.find gvar _s with _ -> (_T gvar_bar)) bexp
                   with
                     Not_found -> bexp
                 ) |->> (bexp, globals) in
               (fun bexp (param, arg) ->
                 let v_param = Term.decode param in
                 let param_bar = Term.encode (fst v_param, [Exp.BAR]) in
                 match arg with
                   Term.EXP (Exp.ADDR _) ->
                    substitute param_bar (_T (_C 100)) bexp
                 | _ ->
                    substitute param_bar (eval _s _L arg) bexp) |->> (bexp', params_args)
             in
             
             dbg "GLO" (f_name ^ "@1:") (m_print "GLO") _s;
             let prime_s si =
               dbg "GLO" (f_name ^ "@2:") (m_print "GLO") _s;
               M.fold (fun key value acc ->
                   let value'' = (fun bexp gvar ->
                       try
                         Term.substitute (_T gvar) (try M.find gvar _s with _ ->
                                                      pf_s "BIABD" Exp.pprint gvar;
                                                      pn_s "BIABD" " in ";
                                                      m_print "BIABD" _s;
                                                      VcpVBase.qvar ();
                           (* raise (StError ("PRECOND-3: " ^ (Exp.to_str gvar) ^ " at " ^ (Locs.to_str l))) *)
                           ) bexp
                       with
                         Not_found -> bexp
                     ) |->> (value, globals) in
                   let value' = (fun bexp (param, arg) ->
                       match arg with
                         Term.EXP (Exp.ADDR _) ->
                          Term.substitute param (_T (_C 100)) bexp
                       | _ ->
                          Term.substitute param (eval _s _L arg) bexp) |->> (value'', params_args) in
                   M.add key value' acc
                 ) si M.empty
             in
             
             let rearrange posts =
               let posts' = (fun (_u, (_,_,_B), (_s,_d,_A)) ->
                   (_u, _B, _s, _d, _A)
                 ) |>>| posts in
               
               posts'
                 (* let subs_f t = (fun t (ed, by) -> Term.map (fun v -> if v=ed then by else Exp.VAR v) t) |->> (t, subs_var) in *)
             in
             
             let d_1' = prime_nonL BExp.substitute d_1 in
             let d_2' = prime_nonL BExp.substitute d_2 in
             let d_3' = prime_nonL BExp.substitute d_3 in
             let d' = BExp.list_to_bexp _d in
             let d_2'' = d' &. d_2' in
             let d_1'' = d' &. d_1' in
             let d_3'' = d' &. d_3' in
             let specs' = rearrange specs in
             dbg "BIABD" ("Number of Specs for " ^ f_name ^ " in " ^ this ^ " is:") pl (List.length specs');
                   
             let has_unsat, _or_di'_l, posts' = (fun (has_unsat, _or_di', acc) (_ui'', _Bi'', _si'', _di'', _Ai'') ->
                 (** sG is the part of _s where variables are global *)
                 dbg "BIABD" "Ai(original):" Formula.pprint [_Ai''];
                 
                 let all_fvs' = (Term.fv _ui'') @@ (concat (BExp.fv |>>| _di'')) @@ (Formula.fv _Bi'') @@ (Formula.fv _Ai'') @@ (M.fold (fun _ v vs -> vs @ Term.fv v) _si'' []) in
                 let all_fvs = (fun v -> Exp.is_hat v || Exp.is_dot v || Exp.is_tilde v || Exp.is_question v || Exp.is_dotdot v || Exp.is_check v) |>- all_fvs' in
                 let fvs_pairs = (fun vv ->
                     let (v,attr) = __V vv in
                     (vv, newvar attr)) |>>| all_fvs in
                 dbg "BIABD" "LINk:" (iterS (fun (a,b) -> p "("; Exp.pprint a; p "->"; Exp.pprint b; p")") ",") fvs_pairs;
                 let _ui = (fun t (v, v') -> Term.substitute (_T v) (_T v') t) |->> (_ui'', fvs_pairs) in
                 let _Bi = (fun t (v, v') -> Formula.usubstitute (_T v) (_T v') t) |->> (_Bi'', fvs_pairs) in
                 let _si = M.map (fun t -> (fun t (v, v') -> Term.substitute (_T v) (_T v') t) |->> (t, fvs_pairs) ) _si'' in
                 let _Ai = (fun t (v, v') -> Formula.usubstitute (_T v) (_T v') t) |->> (_Ai'', fvs_pairs) in
                 dbg "BIABD" "Ai(with fresh vars):" Formula.pprint [_Ai];
                 let _di = (fun d -> (fun d (v,v') -> BExp.substitute (_T v) (_T v') d) |->> (d, fvs_pairs)) |>>| _di'' in
                       
                 let _sii = M.fold (fun k v s -> if M.mem k s then s else M.add k v s) _s _si in
                 let si_G = M.filter (fun key _ -> Exp.is_global key) _sii in
                 
                 (** di' = di[g#:=s(g)] *)
                 dbg "BIABD" "di:" (iterS BExp.pprint "&") _di;
                 dbg "BIABD" "Bi:" Formula.pprint [_Bi];
                 dbg "BIABD" "sii" (m_print "BIABD") _sii;
                 dbg "BIABD" "Ai:" Formula.pprint [_Ai];
                 dbg "BIABD" "siG:" (m_print "BIABD") si_G;
                 
                 let _di' : BExp.t list = (prime_nonL BExp.substitute) |>>| _di in
                 let _Ai' = prime_L Formula.usubstitute _Ai in
                 let _Bi' = prime_L Formula.usubstitute _Bi in
                 dbg "BIABD" "Bi':" Formula.pprint [_Bi'];
                 let to_check = ([], _pure _A @ _d @ _di' @ _pure _Bi',[],[]) in
                 dbg "BIABD" "to SAT check:" Formula.pprint [to_check];
                 (* let fvs = Formula.fv _Bi in *)

                 
                 if (VcpVBase.check_sat2 to_check) then
                   (has_unsat, _or_di', acc @ [(_ui, _sii, _di', _Ai', _Bi', si_G)])
                 else
                   (true, _or_di' @ [BExp.list_to_bexp _di'], acc)
               ) |->> ((false,[],[]), specs') in
             
             let posts_d_2s = (fun (_ui, _sii, _di', _Ai', _Bi', si_G) ->
                 
                 let leftF : Formula.ut = (fun (a,b,c,d) ->
                     let all_b = b @ _d @ _di' in
                     dbg "BIABD" "b & d & di:" (iterS BExp.pprint " & ") all_b;
                     let eval_bddi = BExp.evals all_b in
                     dbg "BIABD" "eval(b & d & di):" (iterS BExp.pprint " & ") eval_bddi;
                     (a, eval_bddi,c,d)) _A in
                 let rightF : Formula.ut = _Bi' in
                 pn_s "BIABD" "Bi-abduction Report: biabd(";
                 pf_s "BIABD" Formula.pprint [leftF]; p_s "BIABD" " * Xi |- Yi * ";
                 pf_s "BIABD" Formula.pprint [rightF]; pn_s "BIABD" ")";
                 let biabd_res_org, d_2_i =
                   try
                     VcpVBase.biabd leftF rightF
                   with
                     e ->
                     pn_s "BIABD" "No Biabduction";
                     [], [_False]
                 in
                 dbg "BIABD" "Number of Biabd results:" pl (List.length biabd_res_org);
                 let biabd_res = reduce_biabd_result biabd_res_org in
                 dbg "BIABD" "Number of Biabd results (reduced):" pl (List.length biabd_res);
                 pause "BIABD";
                 let biabd_res' =
                   (fun ((_, _dij', _Xptr_ij, _Xpred_ij), _Yij) ->
                     let _dij = (fun d ->
                         let fvs = BExp.fv d in
                         not (List.exists (fun vv ->
                                  let (v,_) = __V vv in
                                  Bytes.length v > 2 && Bytes.sub v 0 2 = "%m") fvs)
                       ) |>- _dij' in
                     begin
                       p_s "BIABD" "Xi: ";
                       pf_s "BIABD" Formula.pprint [([], _dij, _Xptr_ij, _Xpred_ij)]; p_s "BIABD" "    ";
                       p_s "BIABD" "Yi: ";
                       pf_s "BIABD" Formula.pprint [_Yij]; pn_s "BIABD" "\n";
                       let si_G' = prime_s si_G in
                       let s_new = M.fold (fun key value acc -> M.add key value acc) si_G' sL in
                       let s_new_ui : Term.t = prime_nonL Term.substitute _ui in (** fixed since _ui is a logical term *)
                       let s_new' = subs (ret attr) s_new_ui s_new in
                       let (_, _, _, _, (structs : Structure.t V.t), _) = packs in
                       let _Yij' = (fun (a,b,c,d) ->  (** @Jul29 *)
                           let c' = (fun (ptr, data) ->
                               let hd = try Term.head (Term.toStr ptr) ptr with e -> Term.pprint ptr; pn "@BIABD_PROC @EXCEPTION IGNORED"; pn (Locs.to_str l); __E ("",[])  in
                               if Exp.is_struct hd then
                                 let tau = Exp.get_struct_name hd in
                                 let (_,fields,_) = try
                                     get_structure structs tau
                                   with
                                     e ->
                                     pn "PROCCALL";
                                     raise e
                                 in
                                 if List.length fields = List.length data then
                                   let data' = List.map2 (fun (f,d) (flde,_) ->
                                                   let (fld,_) = __V flde in
                                                   if f = "" then
                                                     (fld,d)
                                                   else
                                                     (f,d)
                                                 ) data fields in
                                   (ptr, data')
                                 else
                                   (ptr, data)
                               else if List.length data = 1 then
                                 let data' = [("*", snd $$ List.hd data)] in
                                 (ptr, data')
                               else
                                 (ptr, data)
                             ) |>>| c in
                           (a,b,c',d)
                         ) _Yij in
                       let _Xij' = ([], [], _Xptr_ij, _Xpred_ij) in
                       let to_check = _dij @ _pure ((fun (a1,b1,c1,d1) -> (fun (a2,b2,c2,d2) -> (a1@a2, b1@b2, c1@c2, d1@d2)) _Yij) _Ai') in
                       if is_bexp_sat to_check then
                         let _d1 = BExp.evals (_d @@ _di' @@ _dij) in
                         [(s_new', _d1, joinformula _Ai' _Yij', _Xij', [], _L)]
                       else
                         []
                     end
                   ) |>>| biabd_res
                 in
                 biabd_res', d_2_i
               ) |>>| posts' in
             pn_s "BIABD" "Biabd Ends";
             
             let (posts, d_2s) = List.split posts_d_2s in
             let d_2s' = list_to_disj $$ concat d_2s in
             let d_2''' = d_2s' |. d_2'' in
             
             let res' = ((fun (s,d,a,b,v,l) ->
                          let s' = sanitize s args in
                          (s',d,a,b,v,l)
                        ) |>>| (concat (concat posts))) in
             
             let res'' = combine_res res' in
             
             let res = res'' (* @ t1 *) in
             List.iteri (fun i (p,q,r,b,_,_) -> dbg "BIABD" (f_name ^ "@res(" ^ (string_of_int i) ^ "):") (print_post "BIABD" p q r b) l) res;
             pn_s "BIABD" "Proccall Ends";
             dbg "STAT" "PROCCALL:" pl (List.length res);
             
             (res, [], (d_1'', d_2''', d_3''))
         in      

         if EL.is_a_function all_functions f_name  then
           begin
             let (_, (function_name, params, body)) = EL.get_function_details all_functions f_name in
             let attr = Exp.get_attributes function_name in
             (* let (module_name, module_path, attr, (function_name, params, body)) =
               F.find f_name all_functions
             in *)
             begin
               if is_void_pointer attr then
                 begin
                   let params' = (get_var_from_param f_name) |>>| params in
                   let p_a' = List.combine params' args in
                   let body' = toT false body in
                   
                   let decls =
                     (fun decls (p, a) ->
                       let p' =
                         let (v, attr) = Exp.var p in
                         Exp.VAR (v ^ "'", attr)
                       in
                       decls @ [DECL (p', [], Block.INIT_S a, l);
                                DECL (p, [], Block.INIT_S (Term.EXP p'), l)]
                     ) |->> ([], p_a')
                   in
                   
                   let body'' = BLOCK (decls, body', l) in
                   
                   pn_s "UNFOLD" "---------\nThe Void Pointer Body\n-----------";
                   dbg "UNFOLD" (f_name ^ "\n=======\n") pprint body'';

                   let prev_func = !current_function in
                   current_function := Exp.toStr function_name;
                   
                   let (res1, res2, bd, d) = sub_string_body (_s, _d, _A) packs l_X body'' in

                   current_function := prev_func;
                   print_rets "UNFOLD" f_name res2;
                   pn_s "UNFOLD" "\n*************************";
                   let res = (fun (r, s, b, f1, f2) -> (subs (ret attr) r s, b, f1, f2, [], _L)) |>>| res2 in
                   dbg "UNFOLD" "UNFOLD RES:\n" (iterS (fun r -> pprint_f "UNFOLD" r l) "\n") res;
                   (* (true, (attr, _T |>>| params', (specs, d), bd)) *)
                   (res, [], false_d)
                 end
               else
                   (** Find the function name, its parameters, and its triple *)
                   let is_analyzed, (attr, params, ((specs, (d_1,d_2,d_3)) : specs), bd) =               
                     try
                       true, F.find f_name analyzed_functions
                     with
                       Not_found ->
                       try
                         let (_, _, (attr, params, returns, bd, s0)) = List.find (fun (fn,_,_) -> f_name = fn) l_X in
                         let spec = (to_spec s0) |>>| returns in
                         true, (attr, params, (spec, false_d), bd)
                       with
                         Not_found ->
                           begin
                           (** If failed to find this function name,
                               use     the arguments as parameters and
                               {true}        f_name'{true} as its triple
                            *)
                             if f_name |<- currents then
                               e_warn ("Warning (Mutual recursion found): " ^ f_name ) l
                             else
                               if (Bytes.length f_name >= 2) &&
                                    Bytes.sub f_name 0 2 = "#_" then
                                 let s = eval _s _L (Term.encode (f_name, [])) in
                                 let ss = Term.toStr s in
                                 e_warn ("Warning (Function cannot be called): " ^ f_name ^ "=" ^ ss ) l;
                               else
                                 e_warn ("Warning (Function is not found): " ^ f_name ) l;
                             pn_s "BIABD" (f_name ^ " not found");
                             
                             let nv = eval _s _L (Term.EXP (Exp.FCALL (f_name, Term.toExp |>>| args))) in
                             false, ([], args, ([(nv, (M.empty, [], empty), (M.empty, [], empty))], false_d), SKIP(Locs.dummy))
                           end
                   in
                   
                   pn_s "BIABD" ("Proccall " ^ f_name ^ " is continued");
                   compute_proccall is_analyzed attr params specs (d_1,d_2,d_3)
                   
             end
           end
         else
           if VcpBuiltIn.is_builtin f_name then
             let args' = (eval _s _L) |>>| args in
             let (attrs, params, specs) = VcpBuiltIn.get_spec f_name args' in
             
             compute_proccall true attrs params specs false_d
           else
             begin
               (* if not (f_name |<- Shared.builtins) then
               pn (f_name ^ " is not found and skipped"); *)
               ([(_s, _d, _A, empty, [], _L)], [], false_d)
             end
        
      | WHILE (_b, _b_aux, _P, l) ->
         pn_s "INV" "Invariant Analysis Begins";
         let s_b  = eval_b _L _s _b in
         let d1 = BExp.evals (_d @@ [s_b]) in
         let b_sat = is_bexp_sat d1 in
         if b_sat then
           begin
             let ((res1,_,_) as res) : o list * r list * d = precond_loop_invariant _s _d _A _L _b _b_aux _P packs l_X l in
             if List.length res1 > 0 then p_s "INV" "res: ";
             List.iter (fun (s,d,a,b,_,_) ->
                 print_post "INV" s d a b l
               ) res1;
             
             res
           end
         else
           begin
             dbg "INV" "b:" BExp.pprint _b;
             dbg "INV" "s(b):" BExp.pprint s_b;
             dbg "INV" "d:" (iterS BExp.pprint " && ") _d;
             dbg "INV" "s(b) & d:" (iterS BExp.pprint " && ") d1;
             let _U =
               let s_nb = eval_b _L _s $$ BExp.complement _b in
               if VcpVBase.check_sat2 ([], _d @ [s_nb], [], []) then [(_s, _d @ [s_nb], _A, empty, [], _L)] else []
             in
             pn_s "INV" "While condition is UNSAT. The output:";
             List.iter (fun (s,d,a,b,_,_) ->
                 print_post "COMP" s d a b l
               ) _U;
             (_U, [], false_d)
               (* raise (StError "b is unsat in While") *)
           end
      | BLOCK (dc, _p, l) ->
         begin
           dbg "BLOCK" "s:" (m_print "BLOCK") _s;
           match dc with
             [] -> precond (_s, _d, _A, _L) packs l_X _p
           | (DECL (v, _, _, _) as decl)::decls ->
              let _sL, _s_out = M.partition (fun k _ -> k = v) _s in
              dbg "BLOCK" "sL:" (m_print "BLOCK") _sL;
              dbg "BLOCK" "s_out:" (m_print "BLOCK") _s_out;
              
              let (dc_res,_,_) = precond (_s_out, [], empty, F.empty) packs l_X decl in
              let (_sout_s', _, _C, _, _, _) = List.hd dc_res in
              dbg "BLOCK" "(_sout_s',C):" (print_post "BLOCK" _sout_s' [] _C empty) l;
              
              let mergef _ o1 o2 =
                begin
                  match o1, o2 with
                    Some _, _ -> o1
                  | _, Some _ -> o2
                  | None, None -> None
                end
              in

              let decls_p = (fun p d ->
                  comp l d p
                ) |->> (_p, decls) in
              let all_amps = get_amp decls_p in
              let _V = if v |<- all_amps then [v] else [] in
              
              let _E = (fun x -> (Term.EXP (Exp.ADDR x), [("*", M.find x _sout_s')])) |>>| _V in
              dbg "BLOCK" "E:" (iterS Pointer.pprint "*") _E;
           
              let _A_C_E = (fun (a1,b1,c1,d1) -> (fun (a2,b2,c2,d2) -> (a1@a2,b1@b2,c1@c2@_E,d1@d2)) _C) _A in
              

              let _p' = BLOCK (decls, _p, l) in 
              let (res, _X, ds) = precond (_sout_s', _d, _A_C_E, _L) packs l_X _p' in
              pn_s "BLOCK" "Precond for block is done";
              
              let ptr_C = (fun (_, _, ptrs, _) -> fst |>>| ptrs) _C in
              let arr_C = (fun (_, _, _, preds) -> preds) _C in

              let sL_si_fvD _si =
                
                let _si'' = M.filter (fun k _ -> not (k = v)) _si in
                let _si'  = M.merge mergef _sL _si'' in
                _si'
              in

              let _A_m_C (a,b,c,d) =
                let c' = (fun (pt, data) -> not (pt |<- ptr_C)) |>- c in
                let d' = (fun arr -> not (arr |<- arr_C)) |>- d in
                (a,b,c',d')
              in

              let res' = (fun (_si, _di, _Ai, _Bi,xx,yy) ->
                  dbg "BLOCK" "Is:" (print_post "BLOCK" _si _di _Ai _Bi) l;
                  
                  let _si' = sL_si_fvD _si in
                  let _Ai' : Formula.ut = _A_m_C _Ai in
                  dbg "BLOCK" "Is':" (print_post "BLOCK" _si' _di _Ai' _Bi) l;
                  (_si', _di, _Ai', _Bi, xx, yy)
                ) |>>| res in
              let _X' = (fun (_rj, _sj, _dj, _Aj, _Bj) ->
                  dbg "BLOCK" "Js:" (print_post "BLOCK" _sj _dj _Aj _Bj) l;
                  let _sj' = sL_si_fvD _sj in
                  let _Aj' = _A_m_C _Aj in
                  dbg "BLOCK" "Js':" (print_post "BLOCK" _sj' _dj _Aj' _Bj) l;
                  (_rj, _sj', _dj, _Aj', _Bj)
                ) |>>| _X in
              
              (res', _X', ds)
           | _ ->
              [], [], false_d
         end
      | DECL (_x, lens, data, l) ->
         precond_decl _x lens data l
      | RETURN (_x, l) ->
         let _r = eval _s _L _x in
         pn_s "RETURN" ("RETURN @");

         dot ();
         dbg "RETURN" "r:" Term.pprint _r;
         dbg "RETURN" "s:" (m_print "RETURN") _s;
         dbg "RETURN" "d:" (iterS BExp.pprint " & ") _d;
         dbg "RETURN" "A:" Formula.pprint [_A];
         dbg "RETURN" "TIME @ " pn (string_of_float (Sys.time () -. !start_t));
         ([], [(_r, _s, _d, _A, empty)], false_d)
    in
    let res = tmo "precond-end" ((fun (a,b,c,d,e,f) -> (a,b,c,d,e,f)) |>>| res) [] in

    pn_s "COMPLEXITY" "------------------==---------------";
    dbg "COMPLEXITY" "Current Line:" pprint _P;
    dbg "COMPLEXITY" "From P(CONT): " pl (List.length res);
    dbg "COMPLEXITY" "From P(RET): " pl (List.length returns);
    
    (res, returns, ds)

and precond_loop_invariant _s _d _A _L _b _b_aux _P _packs l_X loc : o list * r list * d =
  pn_s "LIST" "Entered into While";
  dbg "INV" "A:" Formula.upprint _A;
  dbg "LIST" "b:" BExp.print _b;

  let rec is_list_mode = function
      BExp.UNIT (t, Op.NE, Term.NULL) when is_list_type t _packs ->
       true
    | BExp.UNIT (t, Op.NE, Term.EXP (Exp.CONST 0)) when is_list_type t _packs ->
       true
    | BExp.UNIT (t, Op.NE, u) when is_list_type t _packs && is_list_type u _packs ->
       true
    | BExp.OP (b, Op.AND, BExp.LBL(_)) ->
       is_list_mode b
    | _ -> false
  in

  match is_list_mode _b with
    true ->
     list_mode _b _s _d _A _P _packs _L l_X loc
  | false ->

     match BExp.get_val $$ BExp.eval _b with
       Some false ->
        pn "Eval to False";
        ([(_s,_d,_A,empty,[],_L)], [], false_d)
     | _ ->
        
        (****** INDEPENDENT FUNCTIONS *******)
        (** s(x) = x-check, s(y)=y-check *)
        let set_check v = _T (Exp.set_check v) in

        (** For all x in xs, Set x -> x-bar to s *)
        let encheck s xs =
          (fun s0 x ->
            M.add x (set_check x) s0
          ) |->> (s, xs)
        in

        let _Base t _Pi =  (** @Jul29 *)
          match t with
            Term.NULL -> Term.NULL
          | Term.EXP (Exp.CONST _) -> t
          | Term.EXP (Exp.VAR _) -> t
          | Term.EXP (Exp.BINOP (Exp.VAR _ as v, Op.ADD, b)) ->
             if Exp.is_hat v && (List.for_all (fun x -> not (Exp.is_hat x)) (Exp.fv b)) then
               Term.EXP v
             else if Exp.is_bar v && (List.for_all (fun x -> not (Exp.is_hat x || Exp.is_bar x)) (Exp.fv b)) then
               Term.EXP v
             else if Exp.is_check v && (List.for_all (fun x -> not (Exp.is_hat x || Exp.is_bar x || Exp.is_check x)) (Exp.fv b)) then
               Term.EXP v
             else
               Term.EXP (Exp.UNDEF)
          | Term.EXP (Exp.BINOP (Exp.BINOP (Exp.VAR _ as v, Op.ADD, c), Op.ADD, b')) ->
             let b = Exp.BINOP (c, Op.ADD, b') in
             if Exp.is_hat v && (List.for_all (fun x -> not (Exp.is_hat x)) (Exp.fv b)) then
               Term.EXP v
             else if Exp.is_bar v && (List.for_all (fun x -> not (Exp.is_hat x || Exp.is_bar x)) (Exp.fv b)) then
               Term.EXP v
             else if Exp.is_check v && (List.for_all (fun x -> not (Exp.is_hat x || Exp.is_bar x || Exp.is_check x)) (Exp.fv b)) then
               Term.EXP v
             else
               Term.EXP (Exp.UNDEF)
          | x -> x
        in


        let ddot nm =
          let (n,a) = __V (VcpVBase.new_log_var ()) in
          let v = (n^"_"^nm, [Exp.DOTDOT]) in
          (Term.encode v =/ _T (_C 0))
        in
        (** sum of list of expressions *)
        let sum_expl = function
            [] -> _C 0
          | c::cs -> (fun c c' -> c @+ c') |->> (c, cs)
        in

        (** (v,c) to v*c *)
        let vc_to_e (v, c) = v @* c in

        (** [(v1,c1);(v2,c2)] to v1*c1 + v2*c2 *)
        let list_to_exp n_l_es =
          sum_expl (vc_to_e |>>| n_l_es)
        in

        (** decompose an expressions from a reference *)
        let decompose exp (var:Exp.t) =
          (** a1*c1 + a2*c2 + l*c3 + l*c4 ... *)
          let es = Exp.sum_of_mul_exp exp in
          (** l*(c3+c4+...) + (a1*c1 + a2*c2) *)
          let (l_e', n_l_es) = List.partition (fun (v, c) -> v = var || c = var) es in
          let cs' = (fun (v, c) -> if v = var then c else v) |>>| l_e' in
          let cs_e = sum_expl cs' in
          (n_l_es, cs_e)
        in

        let decompose_ab exp var =
          let (n_l_es, cs_e) = decompose exp var in
          (list_to_exp n_l_es, cs_e)
        in

        let rec dbl_sq_br exp =
          match exp with
            Exp.UNDEF -> (_NInf, _Inf)
          | Exp.VAR _ as v when Exp.is_question v -> (_NInf, _Inf)
          | Exp.VAR _ -> (exp, exp)
          | Exp.CONST _ -> (exp, exp)
          | Exp.BINOP (x, Op.ADD, y) ->
             let (l1, u1) = dbl_sq_br x in
             let (l2, u2) = dbl_sq_br y in
             (l1 @+ l2, u1 @+ u2)
          | Exp.BINOP (x, Op.SUB, y) ->
             let (l1, u1) = dbl_sq_br x in
             let (l2, u2) = dbl_sq_br y in
             (l1 @- u2, u1 @- l2)
          | Exp.NEG t ->
             let (l, u) = dbl_sq_br t in
             (Exp.NEG l, Exp.NEG u)
          | Exp.BINOP (x, Op.MUL, Exp.CONST c)
            | Exp.BINOP (Exp.CONST c, Op.MUL, x) ->
             let (l, u) = dbl_sq_br x in
             if c >= 0 then
               ((_C c) @* l, (_C c) @* u)
             else
               ((_C c) @* u, (_C c) @* l)
          | Exp.BINOP (x, Op.MOD, Exp.CONST c) ->
             (_C 0, _C (c-1))
          | _ -> (_NInf, _Inf)
        in

        let t_dbl_sq_br = function
            Term.NULL -> (_C 0, _C 0)
          | Term.EXP e -> dbl_sq_br e
        in

        (** for l_max, u is for l_max *)
        let _Bigcup l u a1 b1 a2 b2 =
          if b1 >= 0 && b2 >= 0 then
            (a1 @+ ((_C b1) @* l), a2 @+ ((_C b2) @* u))
          else if b1 >= 0 && b2 < 0 then
            (a1 @+ ((_C b1) @* l), a2 @+ ((_C b2) @* l))
          else if b1 < 0 && b2 >= 0 then
            (a1 @+ ((_C b1) @* u), a2 @+ ((_C b2) @* u))
          else
            (a1 @+ ((_C b1) @* u), a2 @+ ((_C b2) @* l))
        in


        let _Bigcup_lmax (lmax:Exp.t) (a1:Exp.t) (b1:int) (a2:Exp.t) (b2:int) =
          if b1>=0 && b2>=0 then
            (a1, a2 @+ _C b2 @* lmax)
          else if b1>=0 && b2<0 then
            (a1, a2)
          else if b1<0 && b2>=0 then
            (a1 @+ _C b1 @* lmax, a2 @+ _C b2 @* lmax)
          else
            (a1 @+ _C b1 @* lmax, a2)
        in

        let overapproximate coeff a_sub_c =
          match coeff with
            Exp.CONST coeff' ->
             let r = (coeff' / a_sub_c) in
             Exp.CONST r
          | _ ->
             Exp.CONST 0
        in

        let rec __subs_ref b =
          let rec __subs_exp = function
            | Exp.UNDEF
              | Exp.REF _ ->
               let nv = newvar [] in (** Need to be checked *)
               [nv], nv
            | Exp.VAR _ as v when Exp.is_question v ->
               let nv = newvar [] in (** Need to be checked *)
               [nv], nv
            | Exp.FCALL (s, ts) -> [], Exp.FCALL (s, ts)
            | e -> [], e
          in
          let __subs_term = function
              Term.NULL -> [], Term.NULL
            | Term.EXP e ->
               let (nvs, e') = __subs_exp e in
               nvs, Term.EXP (e')
          in
          match b with
            BExp.UNIT (a, op, c) ->
             let (nv1, a') = __subs_term a in
             let (nv2, c') = __subs_term c in
             nv1@nv2, BExp.unit a' op c'
          | BExp.OP   (a, op, c) ->
             let (nv1, a') = __subs_ref a in
             let (nv2, c') = __subs_ref c in
             (nv1@nv2), BExp.op a' op c'
          | _ -> [],b
        in

        let eval_y y s =
          try
            M.find y s
          with
            _ ->
            if Exp.is_global y then
              _T $$ Exp.set_bar y
            else
              begin
                (* pw "s:"; m_print "" _s; *)
                VcpVBase.qvar ()
                              (*          raise (StError ((fst y) ^ " not found in s")) *)
              end
        in

        let var_subs_xz lambda _cs nonlinv si =
          let pair_cs = (fun (x,c) ->
              let sx'' = try M.find x si with _ -> Term.EXP (Exp.UNDEF) in
              let sx' =
                match sx'', c with
                  Term.NULL, _ -> Term.NULL
                | _, Term.NULL -> Term.NULL
                | Term.EXP e, Term.EXP c' -> Term.EXP (e @+ (c' @* lambda))
              in
              let x' = Exp.set_check x in
              (x', sx')) |>>| _cs in
          let pair_zs = (fun z -> (Exp.set_check z, _T (Exp.set_dot z))) |>>| nonlinv in
          dbg "INV" "prime to non-prime:" (iterS (fun (a,b) -> p "("; Exp.pprint a; p ","; Term.pprint b; p ")") ";") (pair_cs @ pair_zs);
          pair_cs @ pair_zs
        in

        let rec make_Di _A'' = function
            BExp.UNIT (Term.EXP (Exp.REF v'), Op.NE, Term.NULL)
          | BExp.UNIT (Term.EXP (Exp.REF v'), Op.NE, Term.EXP (Exp.CONST 0))  ->
             let h = try Exp.head (Exp.toStr v') v' with e -> Exp.pprint v'; pn "@ make_Di"; pn (Locs.to_str loc); raise e  in
             let _a = _Base (_T h) _A'' in
             if not (_a = Term.EXP Exp.UNDEF) then
               let n = _T (newvar []) in (** May need to add CHAR *)
               let l1 = Term.op _a (Term.op n (Term.EXP (_C 1)) Op.SUB) Op.ADD in
               let l2 = Term.op l1 (Term.EXP (_C 1)) Op.ADD in
               [(("Stringpart", [_a;l1]), (l2,[("*",Term.zero)]))]
             else
               []
          | BExp.OP (
BExp.OP (BExp.UNIT (Term.EXP (Exp.REF v'), Op.EQ, lower1), Op.OR, BExp.UNIT (lower2, Op.LE, Term.EXP (Exp.REF ld2))),
Op.AND,
BExp.OP (BExp.UNIT (Term.EXP (Exp.REF ld3), Op.EQ, upper1), Op.OR, BExp.UNIT (Term.EXP (Exp.REF ld4), Op.LE, upper2)) )
               when lower1=lower2 && upper1=upper2 && v'=ld2 && ld2=ld3 && ld3=ld4
            ->
             let h = try Exp.head (Exp.toStr v') v' with e -> Exp.pprint v'; pn "@ make_Di"; pn (Locs.to_str loc); raise e  in
             let _a = _Base (_T h) _A'' in
             if not (_a = Term.EXP Exp.UNDEF) then
               let n = _T (newvar []) in (** May need to add CHAR *)
               let l1 = Term.op _a (Term.op n (Term.EXP (_C 1)) Op.SUB) Op.ADD in
               let l2 = Term.op l1 (Term.EXP (_C 1)) Op.ADD in
               [(("Stringpart", [_a;l1]), (l2,[("*",Term.zero)]))]
             else
               []
          | BExp.OP (x, _, y) ->
             begin
               make_Di _A'' x @@ make_Di _A'' y
             end
          | _ -> []
        in

        (*********** LAMBDA DEPENDENT FUNCTIONS ************)

        let lambda = "lambda" in
        let e_lambda = Exp.VAR (lambda, []) in
        let t_lambda = Term.EXP e_lambda in
        (** t < u ---> a.\ + b *)
        let to_lambda_form exp : (Exp.t * (Exp.t * Exp.t) list) =
          match exp with
            Term.EXP (e) ->
             let (n_l_es, cs_e) = decompose e e_lambda in
             (cs_e, n_l_es)
          | t ->
             (Exp.CONST 0, [])
        in

        let transform_bexp t u (ops:Op.t list) =
          let (a, b_coeff) : (Exp.t * (Exp.t * Exp.t) list) = to_lambda_form t in (** a.\ + ((b1,c1)+(b2,c2)+...) *)
          let (c, d_coeff) : (Exp.t * (Exp.t * Exp.t) list) = to_lambda_form u in (** c.\ + ((d1,__)+(d2,__)+...) *)

          let b = list_to_exp b_coeff in
          let d = list_to_exp d_coeff in

          let d_sub_b = Exp.eval (Exp.BINOP (d, Op.SUB, b)) in (** d - b *)
          if a = c then
            (Term.zero <. Term.EXP d_sub_b) |. (Term.zero == Term.EXP d_sub_b)
          else
            let a_sub_c = Exp.eval (Exp.BINOP (a, Op.SUB, c)) in (** a - c *)
            let fv_db = Exp.fv d_sub_b in (** FV(b-d) *)

            let is_d_sub_b_div_a_sub_c_nonlin = false in

            (** TODO *)
            if is_d_sub_b_div_a_sub_c_nonlin then
              raise (PrecondFails "(d-b)/(a-c) is not linear");
            (** Idea:
             * (d-b)/(a-c) = ((d1c21+d2c22+...)-(b1c11+b2c12+...))/(a-c)
             * ((d1c21+d2c22+...)-(b1c11+b2c12+...))/(a-c) = (d1(c21/(a-c))+d2(c22/(a-c))+...)-(b1(c11/(a-c))+b2(c12/(a-c))+...)
             *)
            let sub x y a_sub_c =
              let o_x = (fun (v,c) -> (v, overapproximate c a_sub_c)) |>>| x in
              let o_y = (fun (v,c) -> (v, overapproximate c a_sub_c)) |>>| y in

              let xe = list_to_exp o_x in
              let ye = list_to_exp o_y in

              Exp.eval (Exp.BINOP (xe, Op.SUB, ye))
            in

            if __E (lambda, []) |<- fv_db then
              BExp._T
            else
              begin
                let res =
                  match a_sub_c with
                  | Exp.CONST x when x > 0 ->
                     Some (t_lambda, Term.EXP (sub d_coeff b_coeff x))
                  | Exp.CONST x when x < 0 ->
                     Some (Term.EXP (sub b_coeff d_coeff (-x)), t_lambda)
                  | Exp.CONST x when x = 0 ->
                     Some (Term.zero, Term.EXP d_sub_b)
                  | _ ->
                     None
                in
                match res with
                  Some (a, b) ->
                   begin
                     match ops with
                       op::[] ->
                        BExp.unit a op b
                     | op1::op2::[] ->
                        BExp.unit a op1 b |. BExp.unit a op2 b
                     | _ -> raise (StError ("LOOP-2: " ^ (Locs.to_str loc)))
                   end
                | None ->
                   BExp._T
              end
        in

        let rec transform = function
            BExp.OP (BExp.UNIT (t1, op1, u1), Op.OR, BExp.UNIT (t2, op2, u2)) when t1=t2 && u1=u2 -> (** <= *)
             transform_bexp t1 u1 [op1; op2]
          | BExp.OP (_, Op.OR, _) -> raise (StError ("LOOP-3: " ^ (Locs.to_str loc))) (** if B(lambda) contains disjunction, precond fails *)
          | BExp.OP (be1, op, be2) ->
             BExp.op (transform be1) op (transform be2)
          | BExp.UNIT (t, op, u) -> (** <,=,/= *)
             transform_bexp t u [op]
          | _ -> BExp._T
        in

        let rec contains_disjunction b =
          match b with
            BExp.OP (_, Op.OR, _) -> true
          | BExp.OP (x, _, y) -> contains_disjunction x || contains_disjunction y
          | _ -> false
        in

        let _tilde_compare di dj = di = dj in (* di_tilde _MVs di = di_tilde _MVs dj *)

        let var_n_diff _si _s0 x : Exp.t * Term.t =
          let xt = _T x in
          (** si(x) *)
          let si_x = eval _si _L xt in
          (** s0(x) *)
          let s0_x = eval _s0 _L xt in

          dbg "INV" ("s0(" ^ (Exp.toStr x) ^ "):") p (Term.toStr s0_x);
          dbg "INV" ("si(" ^ (Exp.toStr x) ^ "):") p (Term.toStr si_x);

          (** si(x)-s0(x). Term.op includes norm and eval *)
          let c = Term.op si_x s0_x Op.SUB in
          dbg "INV" ("c(" ^ (Exp.toStr x) ^ "):") p (Term.toStr c);

          (x, c)
        in

        let partition_btwn_lin_nlin_J =
          List.partition (fun ((x, c'):(Exp.t * Term.t)) -> (** c' is the difference *)
              Term.fv c' = [] && (contains_no_undef_in_term $$ M.find x _s)
            )
        in

        (*
        let partition_btwn_lin_nlin =
          List.partition (fun ((x, c'):(Exp.t * Term.t)) -> (** c' is the difference *)
              match c' with
                Term.NULL -> true
              | Term.EXP c ->
                 let i_s_x =
                   try
                     contains_no_undef_in_term $$ M.find x _s
                   with
                     _ -> true
                 in
                 Exp.fv c = [] && i_s_x (* && equal_in_all x all_s *)
            )
        in
         *)

          
      

        let rec lmax conds _Di = function
          | BExp.OP (
              BExp.OP (BExp.UNIT (Term.EXP (Exp.REF ld1), Op.EQ, lower1), Op.OR, BExp.UNIT (lower2, Op.LE, Term.EXP (Exp.REF ld2))),
              Op.AND,
              BExp.OP (BExp.UNIT (Term.EXP (Exp.REF ld3), Op.EQ, upper1), Op.OR, BExp.UNIT (Term.EXP (Exp.REF ld4), Op.LE, upper2)) )
               when lower1=lower2 && upper1=upper2 && ld1=ld3 && ld2=ld4 && ld1=ld2 ->
             begin
               
               match ld1 with
                 Exp.BINOP (_t, Op.ADD, _l) when _l=e_lambda ->
                  begin
                    let _A_Di : Predicate.t list = (fun (a,b,c,d) -> d @ _Di) _A in
                    
                    try
                      let (_, dt) : Predicate.t = try List.find (fun (nm, dt) -> List.hd dt = Term.EXP _t) _A_Di with _ -> raise (StError "lmax 1") in
                      let l : Term.t = Term.op (List.hd (List.tl dt)) (List.hd dt) Op.SUB in
                      [(Term.toExp l, _True)]
                    with
                      _ -> raise (StError "*(p + (la + lambda)) >= 'c'")
                  end
               | _ -> raise (StError "*(p + (la + lambda)) >= 'c'")
             end
          | BExp.OP (a, Op.AND, b) ->
             let lmax_a : (Exp.t * BExp.t) list = lmax conds _Di a in
             let lmax_b : (Exp.t * BExp.t) list = lmax conds _Di b in
             let res : ((Exp.t * BExp.t) list) =
               concat (
                   (fun (ti, fi) ->
                     concat (
                         (fun (uj, ej) ->
                           dbg "INV" "ti:" Exp.pprint ti;
                           dbg "INV" "fi:" BExp.pprint fi;
                           dbg "INV" "uj:" Exp.pprint uj;
                           dbg "INV" "ej:" BExp.pprint ej;

                           let v1 = Term.EXP ti @<= Term.EXP uj in (* ti <= uj *)
                           let v2 = uj @< ti in (* ti > uj *)

                           let v = fi &. ej in (* fi /\ ej *)
                           let vv1 =
                             if ti = Exp.POSINF || uj = Exp.POSINF then
                               v
                             else
                               v &. v1
                           in (* v3 /\ v1 = fi /\ ej & ti <= uj *)
                           let vv2 =
                             if ti = Exp.POSINF || uj = Exp.POSINF then
                               v
                             else
                               v &. v2 in (* v3 /\ v2 = fi /\ ej & ti > uj *)

                           let r1 =
                             if is_bexp_sat (conds @ [vv1]) then
                               [(ti, vv1)]
                             else
                               []
                           in
                           let r2 =
                             if is_bexp_sat (conds @ [vv2]) then
                               [(uj, vv2)]
                             else
                               []
                           in
                           r1@r2) |>>| lmax_b)) |>>| lmax_a) in
             res
          | BExp.OP (BExp.UNIT (Term.EXP t1, Op.EQ, Term.EXP u1), Op.OR, BExp.UNIT (Term.EXP t2, Op.LE, Term.EXP u2)) (* when t1=t2 && u1=u2 *)
            | BExp.OP (BExp.UNIT (Term.EXP t1, Op.LE, Term.EXP u1), Op.OR, BExp.UNIT (Term.EXP t2, Op.EQ, Term.EXP u2)) when t1=t2 && u1=u2 && t1=e_lambda ->
             [(u1, _True)]
          | BExp.OP (BExp.UNIT (Term.EXP t1, Op.EQ, Term.EXP u1), Op.OR, BExp.UNIT (Term.EXP t2, Op.LE, Term.EXP u2)) (* when t1=t2 && u1=u2 *)
            | BExp.OP (BExp.UNIT (Term.EXP t1, Op.LE, Term.EXP u1), Op.OR, BExp.UNIT (Term.EXP t2, Op.EQ, Term.EXP u2)) when t1=t2 && u1=u2 && u1=e_lambda ->
             [(_Inf, _True)]
          | BExp.UNIT (Term.EXP l, Op.LE, Term.EXP t) when l = e_lambda ->
             [(t @- (_C 1), _True)]
          | BExp.UNIT (Term.EXP t, Op.LE, Term.EXP l) when l = e_lambda ->
             [(_Inf, _True)]
          | BExp.UNIT (Term.EXP l, Op.EQ, Term.EXP t) when l = e_lambda ->
             raise (PrecondFails "t < lambda")
          (* | BExp.UNIT (__c, Op.LE, Term.EXP (Exp.REF (Exp.BINOP (p, Op.ADD, Exp.BINOP (l1, Op.ADD, l2))))) when l2 = e_lambda ->
             begin
               let _A_Di : Predicate.t list = (fun (a,b,c,d) -> d @ _Di) _A in
               try
                 let (_, dt) : Predicate.t = try List.find (fun (nm, dt) -> List.hd dt = Term.EXP p) _A_Di with _ -> raise (StError "lmax 1") in
                 let l = Term.op (List.hd (List.tl dt)) (List.hd dt) Op.SUB in
                 [(Term.toExp (Term.op l (Term.EXP l1) Op.SUB), _True)]
               with
                 _ -> raise (StError "*(p + (la + lambda)) /= NULL")
             end *)
          | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (p, Op.ADD, Exp.BINOP (l1, Op.ADD, l2)))), Op.NE, Term.NULL) when l2 = e_lambda ->
             begin
               let _A_Di : Predicate.t list = (fun (a,b,c,d) -> d @ _Di) _A in
               try
                 let (_, dt) : Predicate.t = try List.find (fun (nm, dt) -> List.hd dt = Term.EXP p) _A_Di with _ -> raise (StError "lmax 1") in
                 let l = Term.op (List.hd (List.tl dt)) (List.hd dt) Op.SUB in
                 [(Term.toExp (Term.op l (Term.EXP l1) Op.SUB), _True)]
               with
                 _ -> raise (StError "*(p + (la + lambda)) /= NULL")
             end
          | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (p, Op.ADD, Exp.BINOP (l1, Op.ADD, l2)))), Op.NE, Term.EXP (Exp.CONST 0))
            | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (Exp.BINOP (p, Op.ADD, l1), Op.ADD, l2))), Op.NE, Term.NULL) when l2 = e_lambda ->
             begin
               let _A_Di : Predicate.t list = (fun (a,b,c,d) -> d @ _Di) _A in
               try
                 let (_, dt) : Predicate.t = try List.find (fun (nm, dt) -> List.hd dt = Term.EXP p) _A_Di with _ -> raise (StError "lmax 1") in
                 let l = Term.op (List.hd (List.tl dt)) (List.hd dt) Op.SUB in
                 [(Term.toExp (Term.op l (Term.EXP l1) Op.SUB), _True)]
               with
                 _ -> raise (StError "*(p + (la + lambda)) /= NULL")
             end
          | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (p, Op.ADD, Exp.BINOP (l1, Op.ADD, l2)))), Op.NE, Term.NULL) ->
             begin
               let _A_Di : Predicate.t list = (fun (a,b,c,d) -> d @ _Di) _A in
               try
                 let (_, dt) : Predicate.t = List.find (fun (nm, dt) -> List.hd dt = Term.EXP p) _A_Di in
                 let l = Term.op (List.hd (List.tl dt)) (List.hd dt) Op.SUB in
                 [(Term.toExp (Term.op l (_T l2) Op.SUB), _True)]
               with
                 _ -> raise (StError "*(p + (lambda + a)) /= NULL")
             end
          | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (p, Op.ADD, Exp.BINOP (l1, Op.ADD, l2)))), Op.NE, Term.EXP (Exp.CONST 0))
            | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (Exp.BINOP (p, Op.ADD, l1), Op.ADD, l2))), Op.NE, Term.NULL) when l1 = e_lambda ->
             begin
               let _A_Di : Predicate.t list = (fun (a,b,c,d) -> d @ _Di) _A in
               try
                 let (_, dt) : Predicate.t = List.find (fun (nm, dt) -> List.hd dt = Term.EXP p) _A_Di in
                 let l = Term.op (List.hd (List.tl dt)) (List.hd dt) Op.SUB in
                 [(Term.toExp (Term.op l (_T l2) Op.SUB), _True)]
               with
                 _ -> raise (StError "*(p + (lambda + a)) /= NULL")
             end
          | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (p, Op.ADD, l1))), Op.NE, Term.NULL)
            | BExp.UNIT (Term.EXP (Exp.REF (Exp.BINOP (p, Op.ADD, l1))), Op.NE, Term.EXP (Exp.CONST 0)) when l1 = e_lambda ->
             begin
               let _A_Di : Predicate.t list = (fun (a,b,c,d) -> d @ _Di) _A in
               try
                 let (_, dt) : Predicate.t = List.find (fun (nm, dt) -> List.hd dt = Term.EXP p) _A_Di in
                 let l = Term.op (List.hd (List.tl dt)) (List.hd dt) Op.SUB in
                 [(Term.toExp (l), BExp._T)]
               with
                 _ ->
                 pn "Error";
                 iterS Predicate.pprint "*" _A_Di;
                 pn "";
                 Exp.pprint p;
                 pn "";
                 raise (StError "*(p + lambda) /= NULL")
             end
          | BExp.UNIT (Term.EXP l, Op.NE, Term.EXP t) when l = e_lambda ->
             if is_bexp_sat conds then
               [(t @- (_C 1), _T (_C 2) @<= _T t);
                (_Inf, t @< _C 0)]
             else
               []
          | BExp.UNIT (Term.EXP l, Op.EQ, Term.EXP t) when l = e_lambda || t = e_lambda ->
             [(_C 0, _True)]
          | x -> [(_Inf, _True)] (* (fun (_, b) -> is_bexp_sat [b]) |>- [(_Inf, x);(Exp.CONST (-1), BExp.complement x)] *)
        in

        let get_lambda_max_sat _smt_xs _di _A_lambda_exp _A'_di =
          let __z = "z" in
          let _t_z = Term.encode (__z, []) in

          let _lambda_p_1 = e_lambda @+ (_C 1) in
          let _A_z = bexp_to_smt_exp $$ BExp.substitute t_lambda _t_z _A_lambda_exp in
          let _A_lambda_p_1 = bexp_to_smt_exp $$ BExp.substitute t_lambda (_T _lambda_p_1) _A_lambda_exp in

          let __C_lambda =
            let __z' = E.Var __z in
            let a'_di_imp_a_lambda = S.all' _smt_xs (_A'_di _A_z) in
            let second = S.not' (S.all' _smt_xs (_A'_di _A_lambda_p_1)) in
            let first = S.all' [__z] (S.(-^>) (S.(<^=) __z' (E.Var lambda)) a'_di_imp_a_lambda) in
            S.bigAnd' [first; second]
          in

          (* let __C_lambda =
            let __z' = E.Var __z in
            let a'_di_imp_a_lambda = S.all' _smt_xs (_A'_di _A_z) in
            let second = S.not' (S.all' _smt_xs (_A'_di _A_lambda_p_1)) in
            let first =   a'_di_imp_a_lambda in
            S.all' [__z] (S.(-^>) (S.(<^=) __z' (E.Var lambda)) ( S.bigAnd' [first; second]))
          in *)

          let _model = __C_lambda in
          dbg "INV" "C(lambda):" p (E.to_string _model);
          let vals =
            match Z.checkSatExp true false _model with
            | SatResult.Model model -> Some model
            | _ -> None
          in

          let res =
            match vals with
              Some val_pairsBN ->
               let val_pairs = List.map (fun (v,bn)->(v,Bignum.to_int bn)) val_pairsBN in
               let (a, b) = try List.find (fun (a, _) -> a = lambda) val_pairs with _ -> raise (StError ("'lambda' not found from biabduction")) in
               dbg "INV" "z [from z3]:" pi b;
               let eb = Exp.CONST b in
               let l1l = e_lambda @< eb |. e_lambda @= eb in
               l1l
            | None ->
               BExp._T
          in

          res
        in

        let l_equiv a b = S.bigAnd' [S.(-^>) a b; S.(-^>) b a] in
        (* let l_and a b = S.bigAnd' [a;b] in *)

        let get_lambda_max_unsat _A_lambda _di _d_0i _xs _ys nonlinv =
          (** TODO: Need condition check *)
          dbg "INV" "A(lambda):" BExp.pprint _A_lambda;
          
          let _A_lambda' = to_linear_b _A_lambda in
          let _A_lambda'' = (fun a_lambda z ->
              let z_dot = _T $$ Exp.set_dot z in
              let zq = _T $$ Exp.set_question z in
              BExp.substitute z_dot zq a_lambda
            ) |->> (_A_lambda', nonlinv) in
          dbg "INV" "A(lambda)'':" BExp.pprint _A_lambda'';
          
          let _B_lambda = approx _A_lambda'' in
          dbg "INV" "B(lambda):" BExp.pprint _B_lambda;
          if contains_disjunction _B_lambda then
            raise (PrecondFails "contains disjunction");

          let _B_tr_lambda_exp : BExp.t =
            let r = transform _B_lambda in
            if is_bexp_linear ~in_terms:[e_lambda] r then
              r
            else
              BExp._T
          in
          dbg "INV" "Transformed B(lambda) as a single formula:" BExp.pprint _B_tr_lambda_exp;

          let _A_lambda_smt = bexp_to_smt_exp _A_lambda in
          let _A_lambda_subs = (fun a_lambda z ->
              let z_dot = _T $$ Exp.set_dot z in
              let (v, attr) = __V z in
              let z_dot' = Term.encode $$ (v^"'", attr) in
              BExp.substitute z_dot z_dot' a_lambda
            ) |->> (_A_lambda, nonlinv) in
          let _A_lambda_subs_smt = bexp_to_smt_exp _A_lambda_subs in
          let _B_lambda_smt = bexp_to_smt_exp _B_tr_lambda_exp in

          dbg "INV" "_A_lambda_subs_smt:" p (E.to_string _A_lambda_subs_smt);
          dbg "INV" "_B_lambda_smt:" p (E.to_string _B_lambda_smt);
          
          let s1 = l_equiv _A_lambda_smt _A_lambda_subs_smt in

          (* let xs = E.fv s1 in
          let smt1 = S.not' (S.all' xs s1) in
          let s2 = l_equiv _A_lambda_smt _B_lambda_smt in
          let ys = E.fv s2 in
          let smt2 = S.all' ys s2 in *)
          let _F_exact = s1 in (* (l_and smt1 smt2) in *)
          dbg "INV" "F_exact:" p (E.to_string _F_exact);

          let has_dot bexp =
            List.exists (fun v -> Exp.is_dot v) (BExp.fv bexp)
          in
          let is_exact = 
            try
              Z.checkSatExpBool _F_exact && not (has_dot _A_lambda)
            with
              x ->
              pn (E.to_string _F_exact);
              raise (StError "F_exact has problem")
          in
          (_B_tr_lambda_exp, is_exact)
        in

        let interval_of_z z _si _cs nonlinv =
          dbg "INV" "Interval of " Exp.pprint z;
          let dot z = _T $$ Exp.set_dot z in
          let a_question () = VcpVBase.qvar () in
          
          let si_z = try M.find z _si with _ -> Exp.pprint z; raise (StError "si_z") in
          dbg "INV" "si(z):" Term.pprint si_z;
          let si_z_zdot = (fun si_z z -> Term.substitute (dot z) (a_question ()) si_z) |->> (si_z, nonlinv) in
          dbg "INV" "si(z)[x-dot := a?]:" Term.pprint si_z_zdot;
          let s_z = try M.find z _s with _ -> Term.EXP Exp.UNDEF in
          dbg "INV" "s(z):" Term.pprint s_z;
          let res1 =
            match si_z_zdot with
              Term.EXP e1 ->
               [(dbl_sq_br e1)]
            | _ -> []
          in
          dbg "INV" "res1:" (iterS (fun (e1,e2) -> Exp.pprint e1; p "~"; Exp.pprint e2) ",") res1;
          (* let res2 =
            match s_z with
              Term.EXP e1 ->
               [(dbl_sq_br e1)]
            | _ -> []
          in
          dbg "INV" "res2:" (iterS (fun (e1,e2) -> Exp.pprint e1; p "~"; Exp.pprint e2) ",") res2; *)
          res1 (* @ res2 *)
        in

        (********** ACTUAL COMPUTATION ***********)

        (** Computing FV and xs *)
        dbg "INV" "Start INV\ns:"  (m_print "INV") _s;
        dbg "INV" "b:" BExp.pprint _b;
        dbg "INV" "A:" Formula.pprint [_A];

        let (_FV, _MVs') = free_mod_v (WHILE (_b, _b_aux, _P, loc)) in
        dbg "INV" "modified variables:" (iterS Exp.pprint ",") _MVs';
        dbg "INV" "free variables:" (iterS Exp.print ",") _FV;

        let fvs = Exp.toStr |>>| _FV in
        let s_out : Term.t M.t = M.filter (fun key value ->
                                   
                                     let r = not ((Exp.toStr key) |<- fvs) in
                                     r
                                   ) _s in
        dbg "INV" "s-FV = s_out:"  (m_print "INV") s_out;

        (** Computing ys = FV - _x *)
        let (_ys, _) = drop_common _FV _MVs' in
        dbg "INV" "non-modified variables:" (iterS Exp.pprint ",") _ys;

        let _MVs = (fun v -> M.mem v _s) |>- _MVs' in

        pn_s "INV" "(1)";
        (** (1) Extrapolation *)
        (** Define s-check(x) = x-check and s-check(y)=s(y) and s-check(L)=s(L).
         *)
        let s_check_temp = encheck M.empty _MVs in
        let _s_check  = (fun s y ->
            let s_y = eval_y y _s in
            try M.add y s_y s  with _ -> raise (StError "s0(temp...)")) |->> (s_check_temp, _ys) in
        dbg "INV" "s_check:" (m_print "INV") _s_check;
        (** Precond(s0, d, A & b, P) = (si,di,Ai,Bi)i *)
        
        let _s_check_b =  eval_b _L _s_check _b in  (** @Jul29 *)
        dbg "INV" "s0(b):" BExp.pprint _s_check_b;
        let s_b = eval_b _L _s _b in

        pn_s "INV" "\nFirst call to precond";
        let _d_pre = BExp.evals (_d @ (* [_s_check_b] @ *) [s_b]) in
        dbg "INV" "d_pre:" (iterS BExp.pprint " & ") _d_pre;
        dbg "INV" "d:" (iterS BExp.pprint " & ") _d;
        dbg "INV" "s_check(b):" BExp.pprint _s_check_b;
        dbg "INV" "s(b):" BExp.pprint s_b;
        
        dbg "INV" "First run starts with:" (print_pre "INV" _s_check _d_pre empty) loc;
        let (_I'', _, (__d_1',__d_2',__d_3')) = precond (_s_check, _d_pre , empty, _L) _packs l_X _P in
        (* let post_fv_count = !VcpVBase.fv in *)
        dbg "INV" "Number of disjunctions:" pl (List.length _I'');

        if List.length _I'' = 0 then
          begin
            pn_s "INV" "No output from 1st precod";
            (* ([], [], false_d) *)
            raise (StError "No disjunct from P in While")
          end
        else
          begin
            List.iter (fun (_si',_di',_Ai',_Bi',_,_) ->
                dbg "INV" "#"  (print_post "INV" _si' _di' _Ai' _Bi') loc
                       
              ) _I'';
            dbg "INV" "|I''|:" pl (List.length _I'');

            (** Computation of d_0i *)
            let _I_d_0is = (fun (((_,_di',_,_,_,_) as o)) ->
                let _d_0i' : BExp.t list = ((fun di' x ->
                                            let x_chk = _T $$ Exp.set_check x in
                                            let s_x = M.find x _s in
                                            (BExp.substitute x_chk s_x) |>>| di') |->> (_di', _MVs)) in
                let _d_0i = BExp.evals _d_0i' in
                dbg "INV" "_d_0i:" (iterS BExp.pprint " & ") _d_0i;
                (o, _d_0i)
              ) |>>| _I'' in

            let __d_1 = ((fun di' x ->
                          let x_chk = _T $$ Exp.set_check x in
                          let s_x = M.find x _s in
                          BExp.substitute x_chk s_x di') |->> (__d_1', _MVs)) in

            let get_pi ((_si,_di',_Ai',_Bi',vi,li), d_0i) =
              let (_,_,all_Bi',_) = _Bi' in
              let pi : Pointer.t list = (fun (pt, _) -> not (List.exists Exp.is_check $$ Term.fv pt)) |>- all_Bi' in
              ((_si,_di',_Ai',_Bi',vi,li), d_0i, pi)
            in

            let _I'_pi = get_pi |>>| _I_d_0is in

            let __F_mod ((_si,_di',_Ai',_Bi',vi,li), d_0i, pi) =
              let fvs = concat (BExp.fv |>>| _di') in
              let check_v = Exp.is_check |>- fvs in
              let is_I_mod = List.length check_v > 0 in

              dbg "INV" "di':" (iterS BExp.pprint " && ") _di';
              dbg "INV" "Imod:" pb is_I_mod;
              
              if is_I_mod then
                dbg "INV" "branch condition depends on check-v(s):" (iterS Exp.pprint ",") check_v;
              let t = if is_I_mod then Op.NE else Op.EQ in
              let _F_mod = bexp_to_smt_exp (BExp.UNIT (_TT ("Fmod", [Exp.DOTDOT]), t, Term.zero)) in
              ((_si,_di',_Ai',_Bi',vi,li), d_0i, (pi, _F_mod, is_I_mod))
            in

            let _I''' = __F_mod |>>| _I'_pi in
            dbg "INV" "Mod is computed. |I'|:" pl (List.length _I''');

            let _I_E_mod, _J = List.partition (fun (_, _, (_,_,b)) -> b) _I''' in
            dbg "INV" "|I_mod|:" pl (List.length _I_E_mod);
            dbg "INV" "|J|:" pl (List.length _J);
            
            let _E_mod, _ = (fun (acc,acc_hd) (_, _, (pi, _, _)) ->
                let pi' = (fun (p,_) -> not (p |<- acc_hd)) |>- pi in
                acc @ pi', acc_hd @ (fst |>>| pi')
              ) |->> (([],[]), _I_E_mod) in
            let _p_mod = fst |>>| _E_mod in
            dbg "INV" "_p_mod:" (iterS Term.pprint " & ") _p_mod;

            let count_res = ref 0 in
            let get_1st_to_2nd_run (((_si',_di',_Ai',_Ci',vi,li), d_0i, (_Ei,_F_mod, is_I_mod)) as inp)  =

              let pi = fst |>>| _Ei in
              let (exs,pures,ptrs,preds) = _Ci' in
              let ptrs' = (fun (pt,_) -> not (pt |<- pi)) |>- ptrs in
              let _Bi' = (exs,pures,ptrs',preds) in
              let si'_b = eval_b _L _si' _b in
              
              dbg "INV" "Second Run strats with:\n" (print_pre "INV" _si' (_di'@[si'_b]) _Ai') loc;
              let (res,_,(__d_1',__d_2',__d_3')) = precond (_si',_di' @ [si'_b],_Ai',_L) _packs l_X _P in
              dbg "INV" "Number of disjunctions in 2nd run:" pl (List.length res);
              dbg "INV" "Second Run ends with:\n" (iterS (fun (a,b,c,d,_,_) -> print_post "INV" a b c d loc) "\n") res;
              count_res := !count_res + List.length res;
              (inp, (res, (_si',_di',_Ai',_Bi',vi,li), (__d_1',__d_2',__d_3')))
            in

            pn_s "INV" "2nd run of _I_E_nonmod";
            let _J_Runs = get_1st_to_2nd_run |>>| _J in
            pn_s "INV" "2nd run of _I_E_mod";
            let _I_E_mod_Runs = get_1st_to_2nd_run |>>| _I_E_mod in

            if !count_res = 0 then
              ([], [], false_d)
            else
              begin
                
                let get_nonmod_lin (inp, (res, _Ii, ds)) =
                  let (_si,_,_,_,_,_) = List.hd res in
                  let (_sii,_,_,_,_,_) = _Ii in
                  let __xzcs : (Exp.t * Term.t) list =
                    (var_n_diff _si _sii) |>>| _MVs
                  in

                  let (_linv, _nonlinv) = partition_btwn_lin_nlin_J __xzcs in
                  (inp, (_Ii, ds, __xzcs, _linv, fst |>>| _nonlinv))
                in
                let _I_E_check_lin = get_nonmod_lin |>>| _J_Runs in

                let get_mod_lin _I_mod =
                  let xzcss = concat ((fun (_, (res, (_sii,_,_,_,_,_), _)) ->
                                  (fun (si,_,_,_,_,_) ->
                                    (var_n_diff si _sii) |>>| _MVs
                                  ) |>>| res
                                ) |>>| _I_mod) in

                  dbg "INV" "xzcss:" (iterS (iterS (fun (k,v) -> Exp.pprint k; p "=>"; Term.pprint v) ",") "; ") xzcss;

                  pn_s "INV" "Checking Linearity";
                  let is_linear (linv, nonlinv) x =
                    dbg "INV" "[Is_linear] x:" Exp.pprint x;
                    let all_c = (fun acc __xzcs ->
                        let (_, c) = List.find (fun (x',_) -> x' = x) __xzcs in
                        acc @@ [c]
                      ) |->> ([], xzcss) in
                    
                    dbg "INV" "all c(x):" (iterS Term.pprint ",") all_c;
                    
                    let is_sx_noundef = contains_no_undef_in_term $$ M.find x _s in
                    if List.length all_c = 0 then
                      (linv, nonlinv)
                    else if not is_sx_noundef then
                      (linv, nonlinv@[(x,List.hd all_c)])
                    else
                      let is_lin = List.for_all (fun c -> Term.is_const c) all_c in
                      if is_lin then
                        let c = List.hd all_c in
                        (linv @ [(x,c)], nonlinv)
                      else
                        let c = List.hd ((fun c -> not (Term.is_const c)) |>- all_c) in
                        (linv, nonlinv @ [(x,c)])
                      (*
                      let c'' = List.hd all_c in
                      dbg "INV" "\nc'':" Term.pprint c'';
                      if Term.is_const c'' &&  List.for_all (fun c' ->
                             dbg "INV" "c':" Term.pprint c';
                             c'' = c') (List.tl all_c) then
                        (linv @ [(x,c'')], nonlinv)
                      else
                        let c''' = List.hd ((fun c -> not (Term.is_const c)) |>- all_c) in
                        (linv, nonlinv @ [(x,c''')]) *)
                  in
                  let _linv, _nonlinv = is_linear |->> (([],[]), _MVs) in
                  dbg "INV" "nonlinv:" (iterS (fun (k, v) -> Exp.pprint k; p "->"; Term.pprint v) ",") _nonlinv;
                  (fun (inp, (res, _Ii, ds)) ->
                    (inp, (_Ii, ds, List.hd xzcss, _linv, fst |>>| _nonlinv))
                  ) |>>| _I_mod
                in
                let _I_E_mod_lin = get_mod_lin _I_E_mod_Runs in

                let partition_btwn_lin_nlin_fld _Ai' _E_check =
                  let (_, _, ptrs, _) = _Ai' in
                  let lin, nonlin = (fun (lin, nonlin) (pts, fields_A) ->
                      try
                        let (_, fields_E) = List.find (fun (p,_) -> p = pts) _E_check in
                        let fields_diff = (fun flds (fnA, dtA) ->
                            let (fnE, dtE) = List.find (fun (fnE,_) -> fnE = fnA) fields_E in
                            flds @ [(fnE, dtE, dtA, Term.eval $$ Term.op dtA dtE Op.SUB)]
                          ) |->> ([], fields_A) in
                        let lin', nonlin' = List.partition (fun (_, _, _, diff) ->
                                                if List.length (Term.fv diff) = 0 then
                                                  true
                                                else
                                                  false
                                                    (*
                                                match diff with
                                                  Term.EXP (Exp.CONST _) -> true
                                                | _ -> false *)
                                              ) fields_diff in
                        let lin'' = (fun (fld, dtE, dtA, diff) ->
                            let w_tld_p = _T $$ newvar [Exp.TILDE] in
                            ((pts, fld), (dtE, w_tld_p @+@ (diff @*@ t_lambda)))) |>>| lin' in
                        let nonlin'' = (fun (fld, dtE, dtA, diff) ->
                            let dtE_tilde = _T (newvar [Exp.TILDE]) in
                            ((pts, fld), (dtE, dtE_tilde))) |>>| nonlin' in
                        lin@lin'', nonlin@nonlin''
                      with
                        _ -> lin, nonlin
                    ) |->> (([],[]), ptrs) in
                  lin, nonlin
                in
            
                let _s0_lambda e_lambda _cs nonlinv s1 =
                  let set_var_subs = var_subs_xz e_lambda _cs nonlinv s1 in
                  (fun acc (ev,s) ->
                    M.add ev s (M.remove ev acc)
                  ) |->> (_s_check, set_var_subs)
                in

                let i_tilde_to_i ((_, _d_0i, (_E_check, _F_mod, is_I_mod)), ((_si',_di',_Ai',_Bi',vi,li), ds, __xzcs, _linv, _nonlinv)) =

                  pn_s "INV" "\nRestoring from checks";
                  (** Linear and non-linear field computation *)
                  let _linf, _nonlinf = partition_btwn_lin_nlin_fld _Ai' _E_check in
                  let lin_var_subs = snd |>>| _linf in
                  let nonlin_var_subs = snd |>>| _nonlinf in
                  let lin_nlin_var_subs = lin_var_subs @ nonlin_var_subs in

                  let ppp = (fun ((a,b),(c,d))-> Term.pprint a; p "."; p b; p "("; Term.pprint c; p ":="; Term.pprint d; p ")") in
                  dbg "INV" "Linear Fields:" (iterS ppp ",") _linf;
                  dbg "INV" "Nonlinear Fields:" (iterS ppp ",") _nonlinf;

                  let _xs = fst |>>| _linv in
                  dbg "INV" "Linear variables:" (iterS Exp.pprint ",") _xs;
                  dbg "INV" "Nonlinear variables:" (iterS Exp.pprint ",") _nonlinv;
                  
                  (** x-check := s(x) *)
                  let check_subs = (fun x ->
                      let x_chk = _T (Exp.set_check x) in
                      let s_x = M.find x _s in
                      (x_chk, s_x)
                    ) |>>| _xs in

                  dbg "INV" "(si',di',Ai',Bi'):\n" (print_post "INV" _si' _di' _Ai' _Bi') (Locs.dummy);
                  let _si_1 = M.map
                              (fun v ->
                                (fun v (to_be, by) ->
                                  Term.substitute to_be by v
                                ) |->> (v, check_subs)
                              ) _si' in 
                  dbg "INV" "s(i)_1:"  (m_print "INV") (_si_1);
                  
                  let set_var_subs_xz = var_subs_xz (e_lambda @- (_C 1)) _linv _nonlinv _si_1 in
                  dbg "INV" "set_var_subs_xz" (iterS (fun (v,t) -> Exp.pprint v; p ":="; Term.pprint t) ", ") set_var_subs_xz;
                  
                  let set_var_subs_xz' = (fun (a,b) -> (_T a, b)) |>>| set_var_subs_xz in

                  let all_var_subs = set_var_subs_xz' @ lin_nlin_var_subs in

                  dbg "INV" "di':" (iterS BExp.pprint " & ") _di';
                  let _di = (substitute_all BExp.substitute all_var_subs) |>>| _di' in
                  dbg "INV" "di:" (iterS BExp.pprint " & ") _di;
                  let _Ai = substitute_all Formula.usubstitute all_var_subs _Ai' in
                  (* let _Pi = _di @ _pure _Ai'' in *)
                  (* let _Ai = _Extend _Ai'' _Pi in *)
                  let _Bi = substitute_all Formula.usubstitute all_var_subs _Bi' in
                  (* let _Bi = _Extend _Bi'' _Pi in *)
                  let _Ei = (fun _E_ (to_be, by) -> (Pointer.substitute to_be by) |>>| _E_) |->> (_E_check, lin_nlin_var_subs) in
                  
                  let _si = M.map (fun v -> substitute_all Term.substitute all_var_subs v) _si' in
                  dbg "INV" "si(2):"  (m_print "INV") (_si);
                  let o' : o = (_si, _di, _Ai, _Bi, vi, li) in

                  let _s0_lambda_i = _s0_lambda (e_lambda @- (_C 1)) _linv _nonlinv _si_1 in
                  dbg "INV" "s0':"  (m_print "INV") (_s0_lambda_i);
                  (* let _b = BExp.ll_to_bexp $$ BExp.dis_norm (BExp.bexp_to_list _b) in *)
                  let _s0_lambda_i_b = eval_b _L _s0_lambda_i _b in
                  let _A_lambda = _s0_lambda_i_b in
                  
                   dbg "INV" "(si,di,Ai,Bi):\n" (print_post "INV" _si _di _Ai _Bi) (Locs.dummy);
                  (((o', (_si_1, _s0_lambda_i, _Ei, _linv, _nonlinv, _di', _d_0i, _A_lambda)), ds), (_E_check,_F_mod,is_I_mod))
                in

                let _I'_to_I (((_si,_di,_Ai,_Bi,vi,li):o), _) =
                  let to_check1 = ([], _di,[],[]) in
                  dbg "INV" "I' to I (to_check1):" Formula.pprint [to_check1];
                  VcpVBase.check_sat2 to_check1 (* && VcpVBase.check_sat2 to_check2 *)
                in

                let has_string _Bi =
                  let (_,_,_,preds) = _Bi in
                  let has = List.exists (fun (nm,_) -> nm = "Stringpart") preds in
                  has
                in

                let _p_mod = (fun acc (_, _, (pi,_,_)) -> acc @ pi) |->> ([], _I_E_mod) in

                let get_Lin _I = (fun (acc,(d1,d2,d3)) branch ->
                    let ((o', (d1',d2',d3')),(_E_check,_F_mod,is_I_mod)) = i_tilde_to_i branch in
                    if _I'_to_I o' then
                      (acc@[((o', (_E_check,_F_mod,is_I_mod,(d1',d2',d3'))))], (d1 |. d1', d2 |. d2', d3 |. d3'))
                    else
                      (acc, (d1,d2,d3))
                  ) |->> (([],(_False,_False,_False)), _I)
                in

                let (_I_mod, (da_1,da_2,da_3)) = get_Lin _I_E_mod_lin in
                let (_I_nonmod, (db_1,db_2,db_3)) = get_Lin _I_E_check_lin in

                let _d_0i_I_mod = list_to_disj (BExp.list_to_bexp |>>| ((fun ((_,(_,_,_,_,_,_,_d_0i,_)),_) -> _d_0i) |>>| _I_mod)) in
                dbg "INV" "d_0i_I_mod:" BExp.pprint _d_0i_I_mod;
                
                let __d_1 = da_1 |. db_1 in
                let __d_2 = da_2 |. db_2 in
                let __d_3 = da_3 |. db_3 in

                let _I'4 = _I_mod @ _I_nonmod in

                dbg "LOOPSTAT" "|I'-unsat|:" pl (List.length _I'4);

                let intv_z_I_mod =
                  let r2 =
                    (fun (((_si,_,_,_,_,_),(_,_,_,_cs,_nonlinv,_,_d_0i,_)),_) ->
                      dbg "INV" "si:" m_print_s _si;
                      
                      
                      let _si_0_1 = _s0_lambda (_C 1) _cs _nonlinv _si in (** NEWLY MODIFIED *)
                      dbg "INV" "si_0_1" m_print_s _si_0_1;
                      
                      let res2 = concat ((fun z ->
                                    
                                     let r = interval_of_z z _si_0_1 _cs _nonlinv in
                                     dbg "INV" "z:" Exp.pprint z;
                                     dbg "INV" "Interval(z):" (iterS (fun (r1,r2) -> p "["; Exp.pprint r1; p ","; Exp.pprint r2; p "]") " ; ") r;
                                     (fun r' -> (z,r')) |>>| r
                                   ) |>>| _nonlinv) in
                      res2
                    ) |>>| _I_mod in
                  let r3 = concat r2 in
                  
                  let all_z = List.sort_uniq (fun v1 v2 -> Exp.compare v1 v2) (fst |>>| r3) in
                  dbg "INV" "r3" (iterS (fun (k,(l,r)) -> Exp.pprint k; p "@["; Exp.pprint l; p ","; Exp.pprint r; p "]") ";") r3;
                  dbg "INV" "all z:" (iterS Exp.pprint ",") all_z;
                  let res2 : (Exp.t * (Term.t * Term.t) list) list =
                    (fun z ->
                      let _I_z = snd |>>| ((fun (z',_) -> z=z') |>- r3) in
                      let _I_z' = (fun (l,u) -> (_T l, _T u)) |>>| _I_z in
                      (z, _I_z')
                    ) |>>| all_z in
                  res2
                in

                let __F_presb ((_postcond, (_s1, _si_0_lambda, _Ei, _cs, nonlinv, _di', _d_0i, _A_lambda)), e1) =
                  let (s1,d1,a1,b1,_,_) = _postcond in
                  print_post "LOOPSTAT" s1 d1 a1 b1 (Locs.dummy);
                  let _a_lambda_smt = bexp_to_smt_exp _A_lambda in
                  let presb_a_lambda_smt = bexp_to_smt_exp $$ VcpVBase.peano_to_pb_b _A_lambda in
                  let s = S.bigAnd' [S.(-^>) _a_lambda_smt presb_a_lambda_smt; S.(-^>) presb_a_lambda_smt _a_lambda_smt] in
                  let xs = E.fv s in
                  let _F_presb_i = S.all' xs s in
                  ((_postcond, (_s1, _si_0_lambda, _Ei, _cs, nonlinv, _di', _d_0i, _A_lambda)), (e1, _F_presb_i))
                in

                let _I = __F_presb |>>| _I'4 (* _I_nomod *) in
                let _I_presb = (fun (_, (_, b)) -> Z.checkSatExpBool b) |>- _I in
                dbg "LOOPSTAT" "|I_presb|:" pl (List.length _I_presb);

                (** END OF (1) *)

                (** (2) Termination Analysis *)
                (** (2-1) *)
                pn_s "INV" "(2)";
                pn_s "INV" "(2-1)";

                (*
                  forall lambda (forall t3'@bar string_c#_14@dot ((t3'@bar!=nil) -> (string_c#_14@dot != nil) OR (t3'@bar!=nil) -> (string_c#_14@dot = nil)))
                 *)

                (** BEGIN each_I *)
                let each_I ((((_si,_di,_Ai,_Bi,_,li) : o) as _postcond, (_s1, _s0_lambda_i, _Ei, (_cs : (Exp.t * Term.t) list), (nonlinv : Exp.t list), (_di':BExp.t list), _d_0i, _A_lambda)), ((_E_check, _F_mod, _is_I_mod, ds), _F_presb)) =

                  dbg "INV" "CLASS " (fun x -> if x = [] then p "True" else iterS BExp.pprint "&" x) _di';
                  dbg "INV" "si:"  (m_print "INV") (_si);
                  dbg "INV" "Non-linear variables:" (iterS Exp.pprint ",") nonlinv;
                  let _xs = fst |>>| _cs in
                  dbg "INV" "Linear variables:" (iterS Exp.pprint ",") _xs;

                  let hs = has_string _Bi in
                  if _is_I_mod && hs then
                    raise (PrecondFails "I_mod Bi is not Emp");

                  let l_A_lambda = BExp.bexp_to_list _A_lambda in
                  let not_A_lambda = BExp.complement _A_lambda in
                  let _A_lambda_smt, not_A_lambda_smt =
                    if List.length l_A_lambda = 1 then
                      (bexp_to_smt_exp _A_lambda, bexp_to_smt_exp not_A_lambda)
                    else
                      let r = E.App (Op.smt_print Op.AND, (bexp_to_smt_exp |>>| (l_A_lambda))) in
                      let r' = S.not' r in
                      (r, r')
                  in


                  (*
                    forall lambda ( forall VARS ( (t3'@bar!=nil) -> (string_c#_14@dot!=nil)) 
                                 OR forall VARS ( (t3'@bar!=nil) -> NOT ( (string_c#_14@dot!=nil))))
                   *)
                  
                  pn_s "INV" ("SMT:: A(lambda): " ^ (E.to_string _A_lambda_smt));
                  pn_s "INV" ("SMT:: not A(lambda): " ^ (E.to_string not_A_lambda_smt));

                  (** xs- and ys *)
                  let smt_xs' = ((<>) lambda) |>- (Exp.toStr |>>| (List.concat (BExp.fv |>>| (_A_lambda :: _d_0i @ _di)))) in
                  let smt_xs = List.sort_uniq Bytes.compare smt_xs' in

                  let xxxxx = (S.bigAnd' (bexp_to_smt_exp |>>| (_d_0i @@ _di))) in
                  let _A'_di x = S.(-^>) xxxxx x in

                  p_s "INV" ("forall lambda ( (forall " ^ (Bytes.concat "," smt_xs) ^ " (");
                  pf_s "INV" (iterS BExp.pprint "&") (_d_0i @@ _di);
                  dbg "INV" "->" (iterS BExp.pprint "&") l_A_lambda;
                  p_s "INV" ("          )) OR (forall " ^ (Bytes.concat "," smt_xs) ^ " (");
                  pf_s "INV" (iterS BExp.pprint "&") (_d_0i @@ _di);
                  dbg "INV" "-> NOT (" (iterS BExp.pprint "&") l_A_lambda;
                  pn_s "INV" "))))";

                  let all' vv e =
                    let vss = List.map (fun v -> (v,S.int')) vv in
                    (* let conds = List.map (fun v -> zero' <^= (Exp.Var v)) vv in
                    let cond = S.bigAnd' conds in *)
                    match List.length vv with
                    | 0 -> e
                    | _ -> S.Exp.All(vss, e)
                  in


                  let _F_independent = S.all' [lambda] (S.bigOr' [(all' smt_xs (_A'_di _A_lambda_smt)); (S.all' smt_xs (_A'_di (not_A_lambda_smt)))]) in
                  pn_s "INV" "to_check:";
                  pn_s "INV" (E.to_string _F_independent);

                  let is_independent = try Z.checkSatExpBool _F_independent with x ->
                                         pn (E.to_string _F_independent);
                                         raise (StError "Sat checking problem") in

                  pn_s "INV" "checkSatExpBool is Done.";
                  if is_independent then pn_s "LOOPSTAT" "Indepenedent";

                  let _B_lambda, is_exact =
                    if is_independent then
                      begin
                        pn_s "INV" "(2-2)";
                        pn_s "INV" "It is SAT";
                        (get_lambda_max_sat smt_xs _di _A_lambda _A'_di, true)   (** (2-2) It does not depend on variables *)
                      end
                    else
                      begin
                        pn_s "INV" "(2-3)";
                        pn_s "INV" "It is UNSAT";
                        get_lambda_max_unsat _A_lambda _di _d_0i _xs _ys nonlinv   (** (2-3) *)
                      end
                  in

                  dbg "INV" "New B(lambda):" BExp.pprint _B_lambda;
                  
                  if is_exact then pn_s "LOOPSTAT" "Exact";
                  pn_s "INV" "(2-4)";
                  
                  let l_b' =
                    if is_exact then
                      msg "INV" "It is exact"
                        []
                    else
                      begin (** TODO: Check it if it is correct *)
                        pn_s "INV" "It is not exact";
                        dbg "INV" "b_aux" (iterS BExp.pprint "&") _b_aux;
                        let s_dot_lambda_i_b_aux = (eval_b' _L _s0_lambda_i) |>>| _b_aux in
                        let _b'' = (* VcpVBase.peano_to_pb_b |>>| *) s_dot_lambda_i_b_aux in
                        let b = (fun b -> not (b = BExp._T) && let fvs = BExp.fv b in not (List.exists (fun v -> Exp.is_dot v || Exp.is_question v) fvs)) |>- _b'' in
                        b
                      end
                  in
                  dbg "INV" "New b':" (iterS BExp.pprint "&") l_b';

                  let plain_mode = l_b' = [] in
                  let _string_mode = not plain_mode in

                  let _A'' =
                    if _is_I_mod then
                      [_d_0i_I_mod]
                    else
                      _di @@ _d_0i
                  in
                  (** Di are missing array, Ri are missing cells *)
                  let _D'i, _R'i = List.split (make_Di _A'' $$ BExp.list_to_bexp l_b') in
                  dbg "INV" "(Di,Ri):" Formula.upprint ([],[],_R'i,_D'i);
                  let _Di = [] in
                  let _Ri = [] in
                  let _b' = BExp.list_to_bexp l_b' in
                  
                  let conds = _A'' in
                  dbg "INV" "(d & di~) OR d_0i_I_mod: " (iterS BExp.pprint "&") conds;

                  if is_bexp_sat conds then
                    pn_s "INV" "CONDS is SAT"
                  else
                    pn_s "INV" "CONDS is UNSAT";

                  let for_lmax' = BExp.OP (BExp.eval _B_lambda, Op.AND, _b') in
                  dbg "INV" "lmax argument(No eval):" BExp.pprint for_lmax';
                  let for_lmax = BExp.eval for_lmax' in
                  dbg "INV" "lmax argument:" BExp.pprint for_lmax;

                  let _lmax_B_lambda' = lmax conds _D'i (for_lmax) in
                  let _lmax_B_lambda'' = (fun (t, e) -> (t, e:: _d_0i )) |>>| _lmax_B_lambda' in
                  let _lmax_B_lambda  = (fun (t, e) ->
                      is_bexp_sat e) |>- _lmax_B_lambda'' in

                  
                  let lambda_maxes = (fun (t,es) ->
                      let es' = BExp.eval $$ BExp.list_to_bexp es in
                      dbg "INV" "lmax^(i,m):" Exp.pprint t; dbg "INV" "d^(i,m):" BExp.pprint es'; pn_s "INV" "";
                      (t, es')) |>>| _lmax_B_lambda in
                  pn_s "INV" "";

                  let _A' = _d_0i in

                  let z_intv : (Exp.t * (Exp.t * Exp.t)) list =
                    let f2 z = interval_of_z z _si _cs nonlinv in
                    let f1 z = (fun lu -> (z,lu)) |>>| (f2 z) in
                    let r1 = f1 |>>| nonlinv in
                    concat r1
                  in

                  let x_intv : (Exp.t * (Exp.t * Exp.t)) list =
                    let f2 z = interval_of_z z _si _cs nonlinv in
                    let f1 z = (fun lu -> (z,lu)) |>>| (f2 z) in
                    let r1 = f1 |>>| _xs in
                    concat r1
                  in

                  dbg "INV" "Number of z intervals:" pl (List.length z_intv);
                  dbg "INV" "z and intervals:" (iterS (fun (z, (l,u)) -> Exp.pprint z; pw ": ["; Exp.pprint l; pw " --"; Exp.pprint u; p "]") ",") z_intv;

                  ((_postcond, _s1, _s0_lambda_i, z_intv, x_intv, lambda_maxes, _Di, _Ri, _cs, nonlinv, _Ei), (_is_I_mod, is_exact, is_independent, _A''))
                in
                (** END each_I *)

                let _I2 = each_I |>>| _I in

                let _I_mod, _I_nomod = List.partition (fun (_,(b,_,_,_)) -> b) _I2 in

                dbg "INV" "|I2|:" pl (List.length _I2);
                dbg "INV" "|I_mod|:" pl (List.length _I_mod);
                dbg "INV" "|I_nomod|:" pl (List.length _I_nomod);
                
                let get_Ci _Ai lmax_m =
                  (* let (_Ci, _Ci') = _Ci_Ci' _Ai in *)
                  let _Ci = _Ai in
                  let (_exs, _pures, _C_ptrs, _C_preds) = _Ci in
                  dbg "INV" "Ci:" Formula.pprint [_Ci];

                  let addr_c = _Addr _Ci in
                  let fst_c = fst |>>| addr_c in
                  let snd_c = snd |>>| addr_c in
                  if (t_lambda |<- fst_c || t_lambda |<- snd_c) && lmax_m = Exp.POSINF then
                    raise (PrecondFails "lambda in Addr(C) AND lmax is Inf");

                  (* (_C_ptrs, _C_preds, _Ci') *)
                  (_C_ptrs, _C_preds)
                in

                let toIntv (_, data) =
                  let aj = Term.toExp (List.hd data) in
                  let bj = Term.toExp (List.hd (List.tl data)) in
                  (aj,bj)
                in

                let divide_Ci _C_preds _II =
                  let _Ci  = _C_preds @ _II in
                  let (_C1_arr, rest) = List.partition (fun (nm, _) -> nm = "Array") _Ci in
                  let (_C2_str, _) = List.partition (fun (nm, _) -> nm = "Stringpart") rest in

                  (** Intervals of Arrays and Stringpart are separated *)
                  let _C1' = toIntv |>>| _C1_arr in
                  let _C2' = toIntv |>>| _C2_str in
                  (_C1', _C2')
                in

                let define_Ckim _s1 lmax_m d_m _Ai _Bi is_exact _Di _cs nonlinv (_si, (_di : BExp.t list), _, _, _, _) =
                  dbg "INV" "\nDisjunct Case " (print_them "INV" [(_si, _di, _Ai, _Bi, [], _L)]) _P;
                  dbg "INV" "L_max" Exp.pprint lmax_m;

                  (** (4) Missing Cells *)
                  let (_C_ptrs, _C_preds) = get_Ci _Ai lmax_m in

                  let (_, _, _B_ptrs, _) = _Bi in
                  let _II = (fun acc (a,t) ->
                      let (c,c') = t_dbl_sq_br a in
                      let _I_in_e_e = c = c' in
                      let fv_e = Exp.fv c in
                      let z_dot_in_e = List.exists Exp.is_dot fv_e in
                      let long_cond = is_exact && _I_in_e_e && not (z_dot_in_e) in
                      dbg "INV" "t:" (iterS (fun (_,b) -> Term.pprint b) ",") t;

                      if long_cond then
                        let letter_b = bexp_to_smt_exp (BExp.UNIT((snd (List.hd t)), Op.NE, Term.EXP (_C 0))) in
                        let _in z l u =
                          match l, u with
                          | Term.EXP Exp.NEGINF, Term.EXP Exp.POSINF -> _True
                          | _, Term.EXP Exp.POSINF -> l @<= z
                          | Term.EXP Exp.NEGINF, _ -> z @<= u
                          | _, _ -> (l @<= z) &. (z @<= u)
                        in

                        let pure2 _A _B =
                          (fun acc (pred, data) ->
                            if pred = "Stringpart" then
                              let _a = List.hd data in
                              let _b = List.hd $$  List.tl data in
                              acc @ ((fun (_p, _qs) ->
                                      let _q = snd (List.hd _qs) in
                                      let _a_q_b = _in _p _a _b in
                                      let _a_q_b_smt = bexp_to_smt_exp _a_q_b in
                                      let _q_ne_0_smt = S.not' (S.(=^=) (term_to_smt_exp _q) S.zero') in
                                      S.(-^>) _a_q_b_smt _q_ne_0_smt
                                    ) |>>| _B)
                            else
                              acc
                          ) |->> ([], _A) in
                        let _pure2_Di_s0lambda_Bi = pure2 _Di _B_ptrs in
                        let _mu = "mu" in
                        let _s0_mu_b = bexp_to_smt_exp $$ eval_b _L (_s0_lambda (Exp.VAR (_mu,[])) _cs nonlinv _s1) _b in
                        let _mu_le_l_s0_mu_b = S.all' ([_mu]) (S.(-^>) (S.(<^=) (S.Exp.Var _mu) (S.Exp.Var lambda)) (_s0_mu_b)) in
                        let _d_im_smt = bexp_to_smt_exp d_m in
                        let _di_smt = bexp_to_smt_exp |>>| _di in
                        let antec' = S.bigAnd' (_mu_le_l_s0_mu_b::_pure2_Di_s0lambda_Bi @ _d_im_smt::_di_smt) in
                        let _xs = fst |>>| _cs in
                        let to_check = S.all' (Exp.toStr |>>| _xs) (S.(-^>) antec' letter_b) in
                        let is_sat = try Z.checkSatExpBool to_check with x -> raise x in
                        if is_sat then
                          acc @ [("Stringpart", [Term.EXP c;Term.EXP c])]
                        else
                          acc @ [("Array", [Term.EXP c;Term.EXP c'])]
                      else
                        acc @ [("Array", [Term.EXP c;Term.EXP c'])]
                    ) |->> ([], _C_ptrs) in

                  let (_C1', _C2') = divide_Ci _C_preds _II in
                  _C1', _C2'
                in

                let define_Bkim _s1 lmax_m d_m _Ai (_si, (_di : BExp.t list), _, _, _, _) =
                  dbg "INV" "\nDisjunct Case " (print_them "INV" [(_si, _di, _Ai, _Ai, [], _L)]) _P;
                  dbg "INV" "L_max" Exp.pprint lmax_m;

                  let (_C_ptrs, _C_preds) = get_Ci _Ai lmax_m in

                  let _II = (fun acc (a,t) ->
                      let (c,c') = t_dbl_sq_br a in
                      acc @ [("Array", [Term.EXP c;Term.EXP c'])]
                    ) |->> ([], _C_ptrs) in

                  let (_C1', _C2') = divide_Ci _C_preds _II in
                  _C1', _C2'
                in

                let define_Mod _s1 lmax_m _Ai (_si, (_di : BExp.t list), _, _Bi, _, _) =
                  dbg "INV" "\nDisjunct Case " (print_them "INV" [(_si, _di, _Ai, _Bi, [], _L)]) _P;
                  dbg "INV" "L_max" Exp.pprint lmax_m;

                  let _Ci = _Bi in

                  let addr_c = _Addr _Ci in
                  let fv_addr_Ci = Exp.toStr |>>| concat ((fun (a,b) -> Term.fv a @ Term.fv b) |>>| addr_c) in
                  let is_fail = lambda |<- fv_addr_Ci && lmax_m = Exp.POSINF in
                  if is_fail then
                    begin
                      dbg "INV" "Ci:" Formula.upprint _Ci;
                      dbg "INV" "Lmax:" Exp.pprint lmax_m;
                      raise (PrecondFails "lambda in Addr of Ci or lmax is INF")
                    end;
                  let (_exs, _pures, _C_ptrs, _C_preds) = _Ci in

                  dbg "INV" "s0_lambda_i(A_i):" Formula.pprint [(_exs, _pures, _C_ptrs, _C_preds)];

                  let _II = (fun (a,t) ->
                      let (c,c') = t_dbl_sq_br a in
                      ("Array", [Term.EXP c;Term.EXP c'])
                    ) |>>|_C_ptrs in

                  let (_C1', _C2') = divide_Ci _C_preds _II in
                  _C1', _C2'
                in

                let is_overlapping _I =
                  let rec aux = function
                      [] -> false
                    | (a1,b1)::xs ->
                       let a1' = a1 in
                       let b1' = b1 in
                       if List.exists (fun (a2,b2) ->
                              let a2' = a2 in
                              let b2' = b2 in
                              let cond = ((a2' @<= a1') &. (a1' @<= b2')) |. ((a2' @<= b1') &. (b1' @<= b2')) in
                              is_bexp_sat [cond]
                            ) xs then true else aux xs
                  in
                  aux _I
                in

                let s_lambda s lambda =
                  M.map
                    (fun v ->
                      Term.eval $$ Term.substitute t_lambda (_T lambda) v
                    ) s
                in

                (** BEGIN loop_cells *)
                let loop_cells _C1 _C2 lmax_m z_intv _A'' _flag =
                  let _Ij = (_C1, _C2) in

                  dbg "INV" "C1:" (iterS (fun (l, u) ->  pw "["; Exp.pprint l; pw " --"; Exp.pprint u; p "]") ",") _C1;
                  dbg "INV" "C2:" (iterS (fun (l, u) ->  pw "["; Exp.pprint l; pw " --"; Exp.pprint u; p "]") ",") _C2;

                  let _Skz (_I : Exp.t * Exp.t) : (Exp.t * Exp.t) =
                    let res =
                      (fun (a, b) (z, (l, u)) ->
                        let z = Exp.set_dot z in
                        let (a1, b1) = decompose_ab a z in
                        let (a2, b2) = decompose_ab b z in
                        match b1, b2 with
                          Exp.CONST b1',Exp.CONST b2' ->
                           _Bigcup l u a1 b1' a2 b2'
                        | _, _ ->
                           raise (PrecondFails "Non-constant")
                      ) |->> (_I, z_intv) in
                    dbg "INV" "Skz(I)=U_{z in [l,u]}Ij:" (fun (l,u) -> pw ": ["; Exp.pprint l; pw " --"; Exp.pprint u; p "]") res;
                    res
                  in

                  let _Sklmax lmax_m _I =
                    let (a,b) = _Skz _I in
                    (** LoopCell Condition : To Understand *)
                    let (a1, b1) = decompose_ab a e_lambda in
                    let (a2, b2) = decompose_ab b e_lambda in
                    match b1, b2 with
                      Exp.CONST b1',Exp.CONST b2' ->
                       _Bigcup_lmax lmax_m a1 b1' a2 b2'
                    | _, _ -> raise (PrecondFails "Non-constant")
                  in

                  let _Iij : ((Exp.t * Exp.t) list * (Exp.t * Exp.t) list) =
                    if lmax_m = Exp.POSINF then
                      (_Skz |>>| (fst _Ij), _Skz |>>| (snd _Ij))
                    else
                      ((_Sklmax lmax_m) |>>| (fst _Ij), (_Sklmax lmax_m) |>>| (snd _Ij)) in

                  dbg "INV" "Iij:" (fun (a,b) ->
                      iterS (fun (l,u) -> pw ": ["; Exp.pprint l; pw " --"; Exp.pprint u; p "]") "," a;
                      p ",";
                      iterS (fun (l,u) -> pw ": ["; Exp.pprint l; pw " --"; Exp.pprint u; p "]") "," b
                    ) _Iij;

                  let fv_I : Exp.t list = (fun (a,b) -> concat ((fun (x,y) -> Exp.fv x @ Exp.fv y) |>>| a) @ concat ((fun (x,y) -> Exp.fv x @ Exp.fv y) |>>| b)) _Iij in
                  if __E (lambda,[]) |<- fv_I then
                    raise (PrecondFails "lamnbda is in Ij");

                  let t_I = (fun (a,b) -> (_T a, _T b)) |>>| (snd _Iij) in
                  if _flag = PRE && lmax_m = Exp.POSINF && is_overlapping t_I then
                    raise (PrecondFails "flag=PRE & lmax=INF & C2 is overlapping");

                  let check_base l u =
                    let base_l = _Base (_T l) _A'' in
                    let base_r = _Base (_T u) _A'' in
                    
                    let res = base_l <> base_r in
                    
                    res
                  in
                  
                  if List.exists (fun (l,u) -> check_base l u) (fst _Iij) then
                    raise (PrecondFails "Base l A'' =/ Base u A'' (1)");
                  if List.exists (fun (l,u) -> check_base l u) (snd _Iij) then
                    raise (PrecondFails "Base l A'' =/ Base u A'' (2)");

                  let (_RiL, _QiN) = _Iij in

                  (************ L ************)
                  (** Convertt Exp.t to Term.t  *)
                  let t_RiL' = (fun (a,b) -> (_T a, _T b)) |>>| (_RiL) in
                  let rec j_tilde_k = function
                      [] -> []
                    | x::xs ->
                       x::(j_tilde_k ((fun (y,_) -> _Base (fst x) _A'' = _Base y _A'') |>- xs))
                  in

                  let t_RiL = j_tilde_k t_RiL' in

                  (** NOTE: type will be updated *)
                  let _I'e'_iLp = (ConvFtoK.max_interval _A'' t_RiL) in
                  dbg "INV" "I'[i][l in L]: " (iterS (fun ((a,b), c) -> p "(["; Term.pprint a; p "--"; Term.pprint b; p "],"; BExp.pprint c; p ")") ",") _I'e'_iLp;

                  let all_I_L   = fst |>>| _I'e'_iLp in
                  dbg "INV" "U(I[l in L]): " (iterS (fun (a,b) -> p "["; Term.pprint a; p "--"; Term.pprint b; p "]") ",") all_I_L;

                  let _e'' = snd |>>| _I'e'_iLp in
                  let rs = (fun (a,b) -> [(_Base a _e'', b)]) |>>| all_I_L in

                  let _S_e = concat ((fun r -> ConvFtoK.union _e'' r) |>>| rs) in

                  dbg "INV" "/\\ e[l in L]: " (iterS BExp.pprint " & ") (_e'');

                  (************ N ************)
                  let t_RiN' = (fun (a,b) -> (_T a, _T b)) |>>| (_QiN) in
                  dbg "INV" "R[i][l in N]: " (iterS (fun (a,b) -> p "["; Term.pprint a; p "--"; Term.pprint b; p "]") ",") t_RiN';

                  let t_RiN = j_tilde_k t_RiN' in

                  let _I'e'_iNp = (ConvFtoK.max_interval _A'' t_RiN) in
                  dbg "INV" "I'[i][l in N]: " (iterS (fun ((a,b), c) -> p "(["; Term.pprint a; p "--"; Term.pprint b; p "],"; BExp.pprint c; p ")") ",") _I'e'_iNp;

                  let _S'_e' =
                    if _flag = POST then
                      ConvFtoK.union _A'' t_RiN
                    else
                      [(t_RiN, BExp._T)]
                  in

                  let res = concat ((fun (_S', _e') -> (fun (_S, _e) ->
                                       if is_overlapping (_S @ _S') then
                                         raise (PrecondFails "S and S' are overlapping");
                                       (_S, _S', [_e;_e'])) |>>| _S_e) |>>| _S'_e') in

                  if List.exists (fun (a,b,_) -> a=b) res then
                    raise (PrecondFails "....");

                  let toArray (a,b) = ("Array", [a;b]) in
                  let toStringpart (a,b) = ("Stringpart", [a;b]) in

                  let res' = ((fun (s,s',e) -> ((toArray |>>| s) @ (toStringpart |>>| s'), e)) |>>| res) in
                  res, res'
                in
                (** END loop_cells *)
                
                let l_dot = Exp.VAR (lambda, [Exp.DOT]) in
                let ld_lmax _lmax_m =
                  let zd_l  = _T (_C 1) @<= _T l_dot in     (** l  <= z. *)
                  let zd_u =  _T l_dot @<= _T _lmax_m in     (** z. < u *)
                  [zd_l; zd_u]
                in
                let _lambda_dot = _T (_C 1) @<= _T l_dot in

                let each_presb ((((_si,_di,_Ai,_Bi,_,li) : o) as _postcond, _s1, _s0_lambda_i, z_intv, x_intv, lambda_maxes, _Di, _Ri, _cs, nonlinv, _Ei), (_, is_exact, is_independent, _A'')) =

                  pn_s "INV" "Each Presb";
                  dbg "INV" "is independent:" pb is_independent;
                  dbg "INV" "is exact:" pb is_exact;
                  let _Zs = concat ((fun (z, (l, u)) ->
                                let z_dot = Exp.set_dot z in (** z. *)
                                let zd_l  = (l @< z_dot) |. (l @= z_dot) in     (** l  <= z. *)
                                let zd_u =  (z_dot @< u) |. (z_dot @= u) in     (** z. < u *)
                                [zd_l &. zd_u]
                              ) |>>| z_intv) in

                  let _Xs = concat ((fun (z, (l, u)) ->
                                let z_dot = Exp.set_dot z in (** z. *)
                                let zd_l  = (l @< z_dot) |. (l @= z_dot) in     (** l  <= z. *)
                                let zd_u =  (z_dot @< u) |. (z_dot @= u) in     (** z. < u *)
                                [zd_l; zd_u]
                              ) |>>| x_intv) in

                  let _Z_subs = (fun z -> (_T $$ Exp.set_dot z, try M.find z _s with _ -> Term.EXP Exp.UNDEF)) |>>| nonlinv in

                  (* let _s_out = M.filter (fun k _ -> Exp.is_global k) _s in *)

                  let _s_lambda_i e_lambda = _s0_lambda_i in

                  
                  let _Zs2' =
                    (fun z ->
                      let t_l_dot = Term.encode (lambda, [Exp.DOT]) in
                      let z' = BExp.substitute t_lambda t_l_dot z in
                      z'
                    ) |>>| _Zs
                  in
                  let _Zs3' =
                    (fun z ->
                      let t_l_dot = Term.encode (lambda, [Exp.DOT]) in
                      let z' = BExp.substitute t_lambda t_l_dot z in
                      let z'' = z' |. z in
                      z''
                    ) |>>| _Zs
                  in

                  let _store_l_dot : Term.t M.t = s_lambda _si l_dot in (* _s0_lambda l_dot _cs nonlinv _s1 in *)
                  let _s_new_l_dot = M.merge (fun key a b -> if a = None then b else a) s_out _store_l_dot in

                  let _z_in = _Zs2' in

                  
                  let for_each_lmax (_lmax_m, _d_im) =

                    pn_s "INV" "For Each Lmax";
                    
                    let _C1_A, _C2_A = ((define_Ckim _s1 _lmax_m _d_im _Ai _Bi is_exact _Di _cs nonlinv) _postcond) in
                    let _, res_A = loop_cells _C1_A _C2_A _lmax_m z_intv [_d_im] POST in
                    let _Ck1_i_m = (fun (preds, e) -> (([],[],[],preds), e)) |>>| res_A in
                    dbg "INV" "|_Ck1_i_m|:" pl (List.length _Ck1_i_m);

                    let _C1_B, _C2_B = ((define_Bkim _s1 _lmax_m _d_im _Bi) _postcond) in
                    let _, res_B = loop_cells _C1_B  _C2_B _lmax_m z_intv [_d_im] PRE in
                    let _Bk_i_m = (fun (preds, e) -> (([],[],[],preds), e)) |>>| res_B in
                    dbg "INV" "|_Bk_i_m|:" pl (List.length _Bk_i_m);
                    
                    
                    let cross' : (Formula.ut * Formula.ut * BExp.t list * BExp.t list) list = concat ((fun (ca,ce) -> (fun (ba,be) -> (ca, ba, ce, be)) |>>| _Bk_i_m) |>>| _Ck1_i_m) in
                    let empty_cross : (Formula.ut * Formula.ut * BExp.t list * BExp.t list) list = [(([],[],[],[]), ([],[],[],[]), [], [])] in
                    let cross = if List.length cross' = 0 then empty_cross else cross' in
                    

                    dbg "INV" "|cross|:" pl (List.length cross);
                    let _Zs1' =
                      (fun z ->
                        let t_l_max = Term.EXP _lmax_m in
                        let z' = BExp.substitute t_lambda t_l_max z in
                        z'
                      ) |>>| _Zs
                    in
                    let _Xs' =
                      (fun z ->
                        let t_l_dot = Term.encode (lambda, [Exp.DOT]) in
                        let z' = BExp.substitute t_lambda t_l_dot z in
                        z'
                      ) |>>| _Xs
                    in
                  
                    let each_k (_Ck1_im, _Bk_im, e'k1_im, ek_im) =
                      pn_s "INV" "Each k";
                      
                      if is_independent || is_exact then
                        begin
                          (** (5-1) *)
                          pn_s "INV" "(5-1) Computing Z";
                          let  lmax_p_1 = _lmax_m in
                          let _store : Term.t M.t = s_lambda _si lmax_p_1 in (* _s_lambda_i lmax_p_1 in *)
                          p_s "INV" "s0_"; pf_s "INV" Exp.pprint lmax_p_1;
                          dbg "INV" ": " (m_print "INV") _store;

                          let _s0_l_max_p_1_nb : BExp.t = eval_b _L _store (BExp.complement _b) in

                          let pure =  ek_im @ e'k1_im @ [_s0_l_max_p_1_nb] @ _Zs1' @ [BExp.complement $$ ddot "F_mod"] @ [ddot "F_presb"] @ [ddot "Findependence" |. ddot "Fexact"] @ [ddot "F_lmax_infty"] in

                          let _leftF = (fun (a,b,c,d) -> [], pure @ b, c @ _Ri ,d @ _Di) _A  in
                          let _rightF = (fun (a,b,c,d) -> (a,b,c@_Ei,d)) _Bk_im in

                          pn_s "INV" "\nbiabd(";
                          pf_s "INV" Formula.pprint [_leftF];
                          pn_s "INV" ",";
                          pf_s "INV" Formula.pprint [_rightF];
                          pn_s "INV" ")";

                          let biabd_res', d_2 = VcpVBase.biabd _leftF _rightF in

                          let is_sat ((_, _djimk, _, _) , _) =
                            let r1 = (fun d (z,z') -> (BExp.substitute z z') |>>| d) |->> (_djimk, _Z_subs) in
                            is_bexp_sat (r1 @ e'k1_im)
                          in
                          let biabd_res = is_sat |>- biabd_res' in
                          dbg "LOOPSTAT" "|biabd|:" pl (List.length biabd_res);
                          let each_biabd ((_, _djimk, _Xptrs, _Xpredicates) , ((_, _, _Yptrs, _Ypredicates) as _Yjimk)) =
                            let _s_new = M.merge (fun key a b -> if a = None then b else a) s_out _store in
                            let (_,_,_C_ptr,_C_pred) = _Ck1_im in
                            let _b_new = _djimk in
                            dbg "INV" "C(ptr):" (iterS Pointer.pprint " * ") _C_ptr;
                            dbg "INV" "C(pred):" (iterS Predicate.pprint " * ") _C_pred;
                            dbg "INV" "Y(ptr):" (iterS Pointer.pprint " * ") _Yptrs;
                            dbg "INV" "Y(pred):" (iterS Predicate.pprint " * ") _Ypredicates;
                            
                            let _A_new = ([],[],_Yptrs @ _C_ptr, _Ypredicates @ _C_pred) in
                            let _B_new = ([],[],_Xptrs @ _Ri, _Xpredicates @ _Di) in
                            (_s_new, _b_new, _A_new, _B_new, [], _L)
                          in
                          (each_biabd |>>| biabd_res, d_2)
                        end
                      else
                        begin
                          (** (5-2) *)
                          pn_s "INV" "(5-2) Computing W";
                          let _s0_l_dot_p_1_nb : BExp.t = eval_b _L _store_l_dot (BExp.complement _b) in

                          let pure = BExp.evals (ek_im @ e'k1_im @ [_s0_l_dot_p_1_nb] @ (ld_lmax _lmax_m) @ _Zs2' @ [BExp.complement $$ ddot "F_mod"] @ [(BExp.complement $$ (ddot "F_presb" &. ddot "Findependence")) |. ddot "Fexact"]) in

                          let _leftF = (fun (a,b,c,d) -> [], pure @ b, c @ _Ri ,d @ _Di) _A  in
                          let _rightF = (fun (a,b,c,d) -> (a,b,c@_Ei,d)) _Bk_im in

                          
                          pn_s "INV" "\nbiabd(";
                          pf_s "INV" Formula.pprint [_leftF];
                          pn_s "INV" ",";
                          pf_s "INV" Formula.pprint [_rightF];
                          pn_s "INV" ")";
                          
                          let biabd_res, d_2 = try
                              VcpVBase.biabd _leftF _rightF
                            with
                              e ->
                              pn "ERROR in BIABD";
                              raise e
                          in
                          
                          (* dbg "LOOPSTAT" "|biabd_res'|:" pl (List.length biabd_res');
                          let is_sat ((_, _djimk, _, _) , _) =
                            dbg "INV" "d_i:" (iterS BExp.pprint " & ") _djimk;
                            let r'1 = is_bexp_sat _djimk in
                            pb r'1; pn "";
                            let r1 = (fun d (z,z') -> (BExp.substitute z z') |>>| d) |->> (_djimk, _Z_subs) in
                            dbg "INV" "d_i[z:=z@dot]:" (iterS BExp.pprint " & ") r1;
                            let r'2 = is_bexp_sat r1 in
                            pb r'2; pn "";
                            dbg "INV" "e'k1_im:" (iterS BExp.pprint " & ") e'k1_im;

                            let r'3 = is_bexp_sat e'k1_im in
                            pb r'3; pn "";
                            
                            let cond = (e'k1_im @ r1) in
                            dbg "INV" "Sat check cond:" (iterS BExp.pprint " & ") cond;
                            let r = is_bexp_sat cond in
                            dbg "INV" "res:" pb r;
                            r
                          in 
                          let biabd_res = is_sat |>- biabd_res' in *)
                          dbg "LOOPSTAT" "|biabd|:" pl (List.length biabd_res);
                          let each_biabd ((_, _djimk, _Xptrs, _Xpredicates) , ((_, _bbbb, _Yptrs, _Ypredicates) as _Yjimk)) =
                            dbg "INV" "djimk:" (iterS BExp.pprint " & ") _djimk; 
                            dbg "INV" "bbb:" (iterS BExp.pprint " & ") _bbbb;
                            let (_,_,_C_ptr,_C_pred) = _Ck1_im in
                            let _b_new = _djimk in
                            let _A_new = ([],[],_Yptrs @ _C_ptr, _Ypredicates @ _C_pred) in
                            let _B_new = ([],[],_Xptrs @ _Ri, _Xpredicates @ _Di) in
                            (_s_new_l_dot, _b_new, _A_new, _B_new, [], _L)
                          in
                          each_biabd |>>| biabd_res, d_2
                        end
                    in
                    
                    let lmax_infty (_Ck1_im, _Bk_im, e'k1_im, ek_im) =

                      let _x_in = _Xs' in
                      let pure =  ek_im @ e'k1_im @ [_lambda_dot] @ _z_in @ [BExp.complement $$ ddot "F_mod"] @ [ddot "F_lmax_infty"] in
                      let _leftF = (fun (a,b,c,d) -> [], pure @ b, c @ _Ri ,d @ _Di) _A  in
                      let _rightF = (fun (a,b,c,d) -> (a,b,c@_Ei,d)) _Bk_im in

                      pn_s "INV" "\nbiabd(";
                      pf_s "INV" Formula.pprint [_leftF];
                      pn_s "INV" ",";
                      pf_s "INV" Formula.pprint [_rightF];
                      pn_s "INV" ")";

                      let biabd_res', d_2 = VcpVBase.biabd _leftF _rightF in

                      let is_sat ((_, _djimk, _, _) , _) =
                        let r1 = (fun d (z,z') -> (BExp.substitute z z') |>>| d) |->> (_djimk, _Z_subs) in
                        is_bexp_sat (r1 @ e'k1_im)
                      in
                      let biabd_res = is_sat |>- biabd_res' in
                      dbg "LOOPSTAT" "|biabd|:" pl (List.length biabd_res);
                      let each_biabd ((_, _djimk, _Xptrs, _Xpredicates) , ((_, _, _Yptrs, _Ypredicates) as _Yjimk)) =
                         dbg "INV" "b(from biabd):" (iterS BExp.pprint " & ") _djimk;
                        let (_,_,_C_ptr,_C_pred) = _Ck1_im in
                        let _b_new = _djimk in
                        let _A_new = ([],[],_Yptrs @ _C_ptr, _Ypredicates @ _C_pred) in
                        let _B_new = ([],[],_Xptrs @ _Ri, _Xpredicates @ _Di) in
                        (_s_new_l_dot, _b_new, _A_new, _B_new, [], _L)
                      in
                      (each_biabd |>>| biabd_res, d_2)
                    in

                    let (res, d_2) : o list * BExp.t =
                      let r =
                        if _lmax_m = Exp.POSINF then
                          begin
                            pn_s "LOOPSTAT" "lmax=INF";
                            lmax_infty |>>| cross
                          end
                        else
                          begin
                            pn_s "LOOPSTAT" "lmax=/INF";
                            each_k |>>| cross
                          end
                      in
                      let (r1, rd) = List.split r in
                      let r2 = concat r1 in
                      dbg "LOOPSTAT" "|Z,W|:" pl (List.length r2);
                      (r2, list_to_disj $$ concat rd)
                    in
                    res, d_2
                  in

                  dbg "LOOPSTAT" "|Lmax|:" pl (List.length lambda_maxes);
                  let rr_ds = for_each_lmax |>>| lambda_maxes in
                  let (rr, d_2) = List.split rr_ds in
                  concat rr, list_to_disj d_2
                in
                  
                let _I_mod =
                  List.mapi (fun i ((a1,a9,_,a2,a3,lmaxes,a4,a5,a6,a7,a8),b) ->
                      let lmaxes' = List.mapi (fun j (lmx, e) -> ((lmx, i, j), e)) lmaxes in
                      ((a1,a9,a2,a3,lmaxes',a4,a5,a6,a7,a8),b)
                    ) _I_mod
                in

                let all_lmaxes' = concat ((fun ((_, _, _, _, lambda_maxes, _, _, _, _, _), _) -> fst |>>| lambda_maxes) |>>| _I_mod) in
                let all_lmaxes = (fun (e, _, _) -> not (e = Exp.POSINF)) |>- all_lmaxes' in

                let is_largest = function
                    Exp.POSINF -> true
                  | lmax ->
                     List.for_all (fun (other, _, _) ->
                         dbg "INV" "other" Exp.pprint other ;
                         let bexp = (other @= lmax) |. (other @< lmax) in
                         dbg "LOOPSTAT" "lmax >= other:" BExp.pprint bexp;
                         is_bexp_sat [bexp]) all_lmaxes
                in

                let lmx_str i m = "lambda_mod_max=(" ^ string_of_int i ^ "," ^ string_of_int m ^ ")" in

                (** TODO: Check if it is necessary *)
                let all_lmx = (fun (_,i,m) -> BExp.complement $$ ddot (lmx_str i m)) |>>| all_lmaxes in

                (** BEGIN each_mod *)
                let each_mod ((((_si,_di,_Ai,_Bi,_,li) : o) as _postcond, _s1, z_intv, x_intv, lambda_maxes, _Di, _Ri, _cs, nonlinv, _Ei), (_, is_exact, is_independent, _A'')) =
                  pn_s "INV" "I in I_mod";

                  print_post "LOOPSTAT" _si _di _Ai _Bi loc;

                  let for_each_lmax ((_lmax_m, i, j), _d_im) =

                    dbg "INV" "for Lmax =" Exp.pprint _lmax_m;
                    
                    if not (is_largest _lmax_m) then
                      begin
                        pn_s "LOOPSTAT" "Not Largest"; 
                        ([], BExp._F)
                      end
                    else
                      begin
                        pn_s "LOOPSTAT" "lmax is Largest";
                        let (_C1_M, _) = define_Mod _s1 _lmax_m _Ai _postcond in
                        dbg "LOOPSTAT" "Before IM:" (iterS (fun (z,ts) ->
                                                         Exp.pprint z; p "@";
                                                         iterS (fun (t1,t2) -> p"[";Term.pprint t1; p","; Term.pprint t2; p"]") "," ts) ",")  intv_z_I_mod;
                        

                        let _z_IM = (fun (z,ts) -> (z, ConvFtoK.max_interval _A'' ts)) |>>| intv_z_I_mod in

                        let is_fail2 = List.exists (fun (z, ts) ->
                                           dbg "LOOPSTAT" "z:" Exp.pprint z;
                                           dbg "LOOPSTAT" "|ts|:" pl (List.length ts);
                                           dbg "LOOPSTAT" "ts:" (iterS (fun ((x1,x2),xb) -> p"([";Term.pprint x1; p","; Term.pprint x2; p "], ";BExp.pprint xb; p ")") ",") ts;
                                           List.length ts > 1 || List.length ts = 0) _z_IM in
                        if is_fail2 then
                          (msg "LOOPSTAT" "FAILS 1") raise (PrecondFails "|z_im|>1|=0");

                        let _z_K2 = (fun (z,ts) ->
                            match ts with
                            | [((l,u),_)] ->
                               (z, (Term.toExp l, Term.toExp u))
                            | _ -> raise (StError "|z_im|>1|=0")) |>>| _z_IM in

                        let (_, _Ck_S) = loop_cells _C1_M [] _lmax_m _z_K2 _A'' MOD in

                        let _Bk_im = concat (fst |>>| _Ck_S) in
                        let _Zs = ((fun (z, (l, u)) ->
                                    let z_dot = Exp.set_dot z in          (** z. *)
                                    let zd_l  = (l @< z_dot)  |. (l @= z_dot) in    (** l  <= z. *)
                                    let zd_u =  (z_dot @< u)  |. (z_dot @= u) in    (** z. < u *)

                                    let s_z = M.find z _s in
                                    let (l2, u2) = dbl_sq_br $$ Term.toExp s_z in
                                    let zd_l2 = (l2 @< z_dot) |. (l2 @= z_dot) in   (** l  <= z. *)
                                    let zd_u2 = (z_dot @< u2) |. (z_dot @= u2) in   (** z. < u *)

                                    (z, zd_l &. zd_u, zd_l2 &. zd_u2)
                                  ) |>>| _z_K2) in
                        let _Zs2' =
                          (fun (z, z_in1, z_in2) ->
                            let t_l_dot = Term.encode (lambda, [Exp.DOT]) in
                            let z_in1' = BExp.substitute t_lambda t_l_dot z_in1 in
                            z_in1' |. z_in2
                          ) |>>| _Zs
                        in

                        let _store_l_dot : Term.t M.t = s_lambda _si l_dot in (* _s0_lambda l_dot _cs nonlinv _s1 in *)
                        dbg "INV" "s_l-dot^(i):" (m_print "INV") _store_l_dot; 

                        dbg "INV" "s_out:" (m_print "INV") s_out;
                        let _s_new_l_dot = M.merge (fun key a b -> if a = None then b else a) s_out _store_l_dot in
                        dbg "INV" "_s_new_l_dot:" (m_print "INV") _s_new_l_dot;
                        
                        let _U2, d_2_U2 =
                          if _lmax_m <> Exp.POSINF then
                            begin
                              (** (U2) *)
                              pn_s "INV" "Computing U2";
                              let _s0_l_dot_p_1_nb : BExp.t = eval_b _L _store_l_dot (BExp.complement _b) in
                              let pure = _A'' @ _Zs2' @ (ld_lmax _lmax_m) @ [_s0_l_dot_p_1_nb] @ (* [ddot "lambda_mod_max=(i,m)"] @ *) [ddot "F_mod"] in
                              dbg "INV" "Pure:" (iterS BExp.pprint " & ") pure;

                              let _leftF = (fun (a,b,c,d) -> [], pure @ b, c @ _Ri ,d @ _Di) _A  in
                              let _rightF = ([],[],_E_mod,_Bk_im) in

                              pn_s "INV" "\nbiabd(";
                              pf_s "INV" Formula.pprint [_leftF];
                              pn_s "INV" ",";
                              pf_s "INV" Formula.pprint [_rightF];
                              pn_s "INV" ")";

                              let biabd_res, d_2 = VcpVBase.biabd _leftF _rightF in
                              dbg "LOOPSTAT" "|biabd|:" pl (List.length biabd_res);

                              let each_biabd ((_, _b_new, _Xptrs, _Xpredicates) , _Y) =
                                let _C = _MakeArray ([],[],[],_Bk_im) in
                                let _A_new = _C *** _Y in
                                let _X : Formula.ut = ([],[],_Xptrs, _Xpredicates) in
                                let _B_new : Formula.ut = _X *** ([],[],_Ri,_Di) in
                                (_s_new_l_dot, _b_new, _A_new, _B_new, [], _L)
                              in
                              each_biabd |>>| biabd_res, list_to_disj d_2
                            end
                          else
                            ([],BExp._F)
                        in

                        let l_max_inf = Exp.POSINF in
                        let (_, _Ck_S) = loop_cells _C1_M [] l_max_inf _z_K2 _A'' MOD in
                        let _Bk_im_inf = concat (fst |>>| _Ck_S) in
                        dbg "LOOPSTAT" "|Bk_im|:" pl (List.length _Bk_im_inf);

                        let _U3, d_2_U3 =
                          (** U3 *)
                          if _lmax_m = Exp.POSINF then
                            begin
                              pn_s "INV" "Computing U3";
                              let pure = _A'' @ [_lambda_dot] @ _Zs2' @ [ddot "F_mod"] @ all_lmx in
                              let _leftF = (fun (a,b,c,d) -> [], pure @ b, c @ _Ri ,d @ _Di) _A  in
                              let _rightF = ([],[],_E_mod,_Bk_im_inf) in
                              
                              pn_s "INV" "\nbiabd(";
                              pf_s "INV" Formula.pprint [_leftF];
                              pn_s "INV" ",";
                              pf_s "INV" Formula.pprint [_rightF];
                              pn_s "INV" ")";

                              let biabd_res, d_2 = VcpVBase.biabd _leftF _rightF in
                              dbg "LOOPSTAT" "|biabd|:" pl (List.length biabd_res);

                              let each_biabd ((_, _b_new, _Xptrs, _Xpredicates) , _Y) =
                               
                                let _C = _MakeArray ([],[],[],_Bk_im_inf) in
                                let _A_new = _C *** _Y in
                                let _X = ([],[],_Xptrs, _Xpredicates) in
                                let _B_new = _X *** ([],[],_Ri,_Di) in
                                (_s_new_l_dot, _b_new, _A_new, _B_new, [], _L)
                              in
                              (each_biabd |>>| biabd_res, list_to_disj d_2)
                            end
                          else
                            ([], BExp._F)
                        in
                        dbg "LOOPSTAT" "|U2|:" pl (List.length _U2);
                        dbg "LOOPSTAT" "|U3|:" pl (List.length _U3);
                        _U2@_U3, d_2_U2 |. d_2_U3
                      end
                  in
                  dbg "LOOPSTAT" "|Lmax|:" pl (List.length lambda_maxes);

                  let rr_ds = for_each_lmax |>>| lambda_maxes in
                  let (rr, d_2) = List.split rr_ds in
                  concat rr, d_2
                in
                (** END each_mod *)
                
                let res_ds = each_presb |>>| _I_nomod in
                let (res, d_2') = List.split res_ds in
                let d_2s = list_to_disj d_2' in
                let _Z_W : o list = concat res in

                dbg "INV" "|I_nomod|" pl (List.length _I_nomod);
                dbg "INV" "|fst(res_ds)|" pl (List.length res);
                dbg "INV" "|Z+W|" pl (List.length _Z_W);
                dbg "INV" "Z+W" (fun () -> iterS (fun x -> pprint_f "INV" x (Locs.dummy)) "\n" _Z_W) ();
                pn_s "INV" "---------------------";

                (** BEGIN U_1 *)
                pn_s "INV" "Computing U1";
                dbg "INV" "A(2nd time):" Formula.upprint _A;
                
                let _U1' =
                  let s_nb = eval_b _L _s $$ BExp.complement _b in
                  if VcpVBase.check_sat2 ([], _d @ [s_nb], [], []) then [(_s, _d @ [s_nb], _A, empty, [], _L)] else []
                in
                let var_subs = (fun (x:Exp.t) -> (_T $$ Exp.set_check x, M.find x _s)) |>>| _MVs in
                let substitutes f t =
                  (fun t (to_be, by) -> f to_be by t) |->> (t, var_subs)
                in

                dbg "INV" "_I'':" (fun () -> iterS (fun x -> pprint_f "INV" x (Locs.dummy)) "\n" _I'') ();
                let _I''1 = (fun (_si',_di',_Ai',_Bi',vi,li) ->
                    let _si'' = M.map (fun v -> substitutes Term.substitute v ) _si' in
                    let _di'' = (substitutes BExp.substitute) |>>| _di' in
                    let _Ai'' = substitutes Formula.usubstitute _Ai' in
                    dbg "INV" "before subs:" Formula.upprint _Bi';
                    let _Bi'' = substitutes Formula.usubstitute _Bi' in
                    dbg "INV" "after subs:" Formula.upprint _Bi'';
                    
                    let _si'_nb = eval_b _L _si'' (BExp.complement _b) in
                    (* dbg "INV" "_si'_nb:" BExp.pprint _si'_nb; *)
                    (_si'', _di''@[_si'_nb], _Ai'', _Bi'', vi, li)
                  ) |>>| _I'' in

                dbg "INV" "_I''1:" (fun () -> iterS (fun x -> pprint_f "INV" x (Locs.dummy)) "\n" _I''1) ();
                
                let _I''2 = (fun (_si'', _di'', _Ai'', _Bi'', vi, li) -> is_bexp_sat _di'') |>- _I''1 in
                dbg "INV" "|_U1'|" pl (List.length _U1');
                dbg "INV" "_U1'" (fun () -> iterS (fun x -> pprint_f "INV" x (Locs.dummy)) "\n" _U1') ();
                pn_s "INV" "---==---------------==---";

                dbg "INV" "|_I''2|" pl (List.length _I''2);
                dbg "INV" "_I''2" (fun () -> iterS (fun x -> pprint_f "INV" x (Locs.dummy)) "\n" _I''2) ();
                pn_s "INV" "---==---------------==---";
                
                let get_U1 (_si',_di',_Ai',_Bi',vi,li) =
                  let _leftF = (fun (a,b,c,d) -> (a,b@_di',c,d)) _A in
                  let _rightF = _Bi' in
                  
                  pn_s "INV" "\nbiabd(";
                  pf_s "INV" Formula.pprint [_leftF];
                  pn_s "INV" ",";
                  pf_s "INV" Formula.pprint [_rightF];
                  pn_s "INV" ")";

                  let biabd_res, d_2 = VcpVBase.biabd _leftF _rightF in
                  (* let is_sat ((_, _djimk, _, _) , _) =
                    let r1 = (fun d (z,z') -> (BExp.substitute z z') |>>| d) |->> (_djimk, _Z_subs) in
                    is_bexp_sat (r1 @ e'k1_im)
                  in
                  let biabd_res = is_sat |>- biabd_res' in *)
                  dbg "LOOPSTAT" "|biabd|:" pl (List.length biabd_res);
                  let each_biabd ((_, _djimk, _Xptrs, _Xpredicates) , ((_, _, _Yptrs, _Ypredicates) as _Yjimk)) =
                    let _s_new = _si' in
                    let (_,_,_C_ptr,_C_pred) = _Ai'  in
                    let _b_new = _djimk in
                    dbg "INV" "C(ptr):" (iterS Pointer.pprint " * ") _C_ptr;
                    dbg "INV" "C(pred):" (iterS Predicate.pprint " * ") _C_pred;
                    dbg "INV" "Y(ptr):" (iterS Pointer.pprint " * ") _Yptrs;
                    dbg "INV" "Y(pred):" (iterS Predicate.pprint " * ") _Ypredicates;
                    dbg "INV" "_b_new:" (iterS BExp.pprint " & ") _b_new;
                    let _A_new = ([],[],_Yptrs @ _C_ptr, _Ypredicates @ _C_pred) in
                    let _B_new = ([],[],_Xptrs, _Xpredicates) in
                    (_s_new, _b_new, _A_new, _B_new, [], _L)
                    
                  in
                  (each_biabd |>>| biabd_res)
                in

                let _U_I' = List.concat (get_U1 |>>| _I''2) in

                let _U1 = _U1' @ _U_I' in
                (** END U_1 *)
                
                dbg "LOOPSTAT" "|I_mod|:" pl (List.length _I_mod);
                let res_Us = each_mod |>>| _I_mod in
                dbg "INV" "|res_Us|:" pl (List.length res_Us);
                let (res1, res2) = List.split res_Us in
                let _U2_U3 = concat res1 in
                dbg "INV" "|_U2_U3|:" pl (List.length _U2_U3);
                dbg "INV" "_U2_U3:\n" (fun () -> iterS (fun x -> pprint_f "INV" x (Locs.dummy)) "\n" _U2_U3) ();
                pn_s "INV" "---==---------------==---";
                
                let d_2_Us = list_to_disj (concat res2) in

                let res = _Z_W @ _U1 @ _U2_U3 in
                pn_s "INV" "Total number of postconditions:";
                pf_s "INV" pi (List.length res);
                dbg "STAT" "WHILE:" pl (List.length res);
                (res, [], (_False, d_2s |. d_2_Us, _False))
              end
          end
        
and list_mode _b _s _d _A _P packs _L l_X _loc =
  dbg "LIST" "List Mode:" (print_pre "LIST" _s _d _A) _loc;
  dbg "LIST" "b:" BExp.pprint _b;


  let _pprint (s, d, b) =
    dbg "LIST" "s:" (m_print "LIST") s;
    dbg "LIST" "d:" (iterS BExp.pprint " & ") d;
    dbg "LIST" "A:" Formula.upprint b
  in

  let pprint_S (sdb, _) =
    pn_s "LIST" "--------";
    pn_s "LIST" "(s,d,A)";
    _pprint sdb;
    pn_s "LIST" "........"
  in

  let pprint_H h =
    pn_s "LIST" "--------";
    pn_s "LIST" "H";
    iterS _pprint "*****\n" h;
    pn_s "LIST" "........"
  in

  let pprint_INV inv =
    pn_s "LIST" "--------";
    pn_s "LIST" "INV";
    iterS _pprint "*****\n" inv;
    pn_s "LIST" "........"
  in

  match _b with
    BExp.UNIT (_t, Op.NE, _u) ->
     pn_s "LIST1" "Pattern Matched";

     let __ls = ("List", [eval _s _L _t; eval _s _L _u]) in
     let (_,_,ptrs_A,preds_A) = _A in
     let _B : Formula.ut = if __ls |<- preds_A then empty else ([],[],[],[__ls]) in
     dbg "LIST1" "B:" Formula.upprint _B;

     let init_state = (_s,_d,_B *** _A) in
     let _S = [(init_state, [])] in
     iterS pprint_S "" _S;

     let _V = [] in
     let _Inv = [init_state] in
     pn_s "LIST1" "Loop Started";
     let rec _while counter _V _Inv _S =
       dbg "LIST" "counter:" pl counter;
       dbg "LIST1" "|S|:" pl (List.length _S);

       if counter > 40 then
         (_V, _Inv)
       else if List.length _S = 0 then
         (_V, _Inv)
       else
         begin
           let ((_si,_di,_Ai), _H) = List.hd _S in
           dbg "LIST" "HD(S):\n" pprint_S (List.hd _S);

           let _S = List.tl _S in
           let _H = _H @ [(_si, _di, _Ai)] in
           dbg "LIST0" "H:" pprint_H _H;

           (* let _Inv = _Inv @ [(_si, _di, _Ai)] in *)
           dbg "LIST" "INV:" pprint_INV _Inv;

           pn_s "LIST1" "Precond is called";
           dbg "LIST1" "P:" pprint _P;
           let _si_b = eval_b _L _si _b in
           let (_S', _, _) = precond (_si, BExp.(_di &&. _si_b) , _Ai, _L) packs l_X _P in
           
           dbg "LIST" "S':\n" (iterS (fun (si,di,ai,bi,_,_) -> print_post "LIST" si di ai bi _loc) "")  _S';

           if List.exists (fun (_,_,_,_B,_,_) -> not(_B = empty)) _S' then
             raise (PrecondFails "_B' is not emp");

           let _normalize (s,d,a,b,q,r) =
             let (s',d',a') = normalize (s,d,a) in
             (s',d',a',b,q,r)
           in
           let _S' = _normalize |>>| _S' in
           dbg "LIST" "Norm(S'):" (iterS (fun (si,di,ai,bi,_,_) -> print_post "LIST" si di ai bi _loc) "")  _S';

           let _V, _S' = (fun (_V, _S') ((_s',_d',_A',_,_,_) as r) ->
               let sigma = (fun sigma (_s,_d,_A) ->

                   pn_s "LIST3" "\n--------------\nNow comparing";
                   dbg "LIST3" "(s'',d'',A'')\n" _pprint (_s,_d,_A); 
                   pn_s "LIST3" "and";
                   dbg "LIST3" "(s',d',A')\n" _pprint (_s',_d',_A'); 
                   
                   match sigma with
                     None -> (try get_sigma (_s,_d,_A) (_s',_d',_A') with err -> pn "Error at List mode"; raise err)
                   | _ -> sigma) |->> (None, _Inv) in
               match sigma with
                 None -> pn_s "LIST" "No Sigma"; (_V, _S' @ [r])
               | Some s -> dbg "LIST" "Sigma Found.\nsigma:" (iterS (fun (q1,q2) -> Term.pprint q1; p "->"; Term.pprint q2) ",") s;
                           (_V @ (fst |>>| s), _S')
             ) |->> ((_V, []), _S') in

           dbg "LIST1" "(After Sigma/V) S':" (iterS (fun (si,di,ai,bi,_,_) -> print_post "LIST" si di ai bi _loc) "")  _S';

           let _S = (fun _S (s',d',a',_,_,_) -> _S @ [((s',d',a'), _H)]) |->> (_S, _S') in

           let _Inv = _Inv @ ((fun (s',d',a',_,_,_) -> (s',d',a')) |>>| _S') in
           
           _while (counter+1) _V _Inv _S
         end
     in
     let _V', _Inv = _while 1 _V _Inv _S in
     pn_s "LIST" "End of Loop";
     dbg "LIST" "V':" (iterS (fun a -> Term.pprint a) ",") _V';

     let map_to_fresh _V = (fun v -> (v, _T (newvar [Exp.TILDE]))) |>>| _V in
     let rho = map_to_fresh _V' in
     
     let comp rho s' = M.map (fun v -> (fun v (to_be, by) -> Term.substitute to_be by v) |->> (v, rho)) s' in
     let res = (* (fun (((_, e_j, _X_ptrs, _X_preds), _Yj)) -> *)
       (fun (s',d',a') ->
         let s'' = comp rho s' in
         let s'_nb = eval_b _L s'' (BExp.complement _b) in
         let d'' = (substitute_all BExp.substitute rho) |>>| d' in
         let _A'' = substitute_all Formula.usubstitute rho a' in
         (* let _Xj = ([],[],_X_ptrs,_X_preds) in *)
         let r : o = (s'', d'' @ [s'_nb] (* @ e_j *), _A'' (* ***_Yj *), _B (* _Xj *), [], _L) in
         dbg "LIST1" "r:" (pprint_f "LIST" r) _loc;
         r
       ) |>>| _Inv (* ) |>>| biabd_res *) in 
     (res, [], false_d)
  | _ ->
     ([],[],false_d)

and sub_string_body (_s, _, _A) packs l_X _P =
  let rec subs_string_prog _s _A _P =
    match _P with
      ASSIGN (_x, _t, l) ->
       let (_t', _s', _A', s_subs) = subs_string_term _s _A _t in
       let _P' = ASSIGN (_x, _t', l) in
       (_P', _s', _A', s_subs)
    | IF (_b, _P1, _P2, l) ->
       let (_P1', _s1', _A1', s_subs1) = subs_string_prog _s   _A   _P1 in
       let (_P2', _s2', _A2', s_subs2) = subs_string_prog _s1' _A1' _P2 in
       (IF (_b, _P1', _P2', l), _s2', _A2', s_subs1 @ s_subs2)
    | COMP (_P1, _P2, l) ->
       let (_P1', _s1', _A1', s_subs1) = subs_string_prog _s   _A   _P1 in
       let (_P2', _s2', _A2', s_subs2) = subs_string_prog _s1' _A1' _P2 in
       (COMP (_P1', _P2', l), _s2', _A2', s_subs1 @ s_subs2)
    | MALLOC (_x, _z, l) ->
       (MALLOC (_x, _z, l), _s, _A, []) (** May need to revise *)
    | SARRAY (_x, _y, _z, l) ->
       (SARRAY (_x, _y, _z, l), _s, _A, []) (** May need to revise *)
    | LOOKUP (_x, _p, _f, l) ->
       (LOOKUP (_x, _p, _f, l), _s, _A, [])
    | MUTATION (_p, _f, _t, l) ->
       let (_t', _s', _A', s_subs) = subs_string_term _s _A _t in
       let _P' = MUTATION (_p, _f, _t', l) in
       (_P', _s', _A', s_subs)
    | DISPOSE (_x, l) ->
       (DISPOSE (_x, l), _s, _A, [])
    | WHILE (_b, _bs, _P1, l) ->
       let (_P1', _s1', _A1', s_subs1) = subs_string_prog _s _A _P1 in
       (WHILE (_b, _bs, _P1', l), _s1', _A1', s_subs1)
    | PROCCALL (_x, _args, l) ->
       let (_args', _s', _A', s_subs) =
         (fun (acc_args, _s, _A, acc_s_subs) _t ->
           let (_t', _s', _A', s_subs) = subs_string_term _s _A _t in
           (acc_args @ [_t'], _s', _A', acc_s_subs @ s_subs)
         ) |->> (([], _s, _A, []), _args) in
       (PROCCALL (_x, _args', l), _s', _A', s_subs)
    | BLOCK (dc, _P1, l) ->
       (* let (dc', _s0', _A0', s_subs0) = (fun (dc', _s0', _A0', s_subs0) d ->
           let (d', _s', _A', s_subs00) =  subs_string_prog _s0' _A0' d in
           (dc'@[d'], _s', _A', s_subs0@s_subs00)
         ) |->> (([],_s,_A,[]), dc) in *)
       (* let (_P1', _s1', _A1', s_subs1) = subs_string_prog _s0' _A0' _P1 in *)
       let (_P1', _s1', _A1', s_subs1) = subs_string_prog _s _A _P1 in
       (BLOCK (dc, _P1', l), _s1', _A1', s_subs1)
    | DECL (_x, _len, _data, l) ->
       begin
         match _data with
           Block.INIT_M (((Block.INIT_S (Term.EXP (Exp.STRING s)))::_) as _data') ->
            let (_data', _s, _A, s_subs) =
              (fun (_data, _s, _A, s_subs) _t' ->
                match _t' with
                  Block.INIT_S _t ->
                  let (_t', _s', _A', s_subs') = subs_string_term _s _A _t in
                  (_data @ [Block.INIT_S _t'], _s', _A', s_subs @ s_subs')
                | _ ->
                   (_data, _s, _A, s_subs)
              ) |->> (([], _s, _A, []), _data') in
            let len' = if List.length _data' > 1 then
                         [_C (List.length _data')]
                       else
                         []
            in
            (DECL (_x, len', Block.INIT_M _data', l), _s, _A, s_subs)
         | _ ->
            (DECL (_x, _len, _data, l), _s, _A, [])
       end
    | RETURN (_x, l) ->
       (RETURN (_x, l), _s, _A, [])
    | SKIP l ->
       (SKIP (l), _s, _A, [])
    | LABEL (lbl, el, l) ->
       (LABEL (lbl, el, l), _s, _A, [])
    | FAIL ->
       (FAIL, _s, _A, [])
  in
  let _P', _s', _A', s_subs = subs_string_prog _s _A _P in
  dbg "GLO" "After SUBSTR (s'):" (m_print "GLO") _s';
  let (res1, (res2 : (Term.t * Term.t M.t * BExp.t list * Formula.ut * Formula.ut) list), ds) =
    precond (_s', [], _A', F.empty) packs l_X _P' in
  let res1' = (res_maker s_subs) |>>| res1 in
  dbg "SUBSTR" "Before Precond:" (print_pre "SUBSTR" _s' [] _A') (Locs.dummy);
  dbg "SUBSTR" "After Precond:" (List.iter (fun (_,s,d,a,b) -> print_post "SUBSTR" s d a b (Locs.dummy))) res2;
  dbg "SUBSTR" "s_subs:" (iterS (fun (a,b,c) -> Exp.pprint a; p ","; Pointer.pprint b; p ","; Predicate.pprint c) ",") s_subs;

  let res2' : (Term.t * Term.t M.t * BExp.t list * Formula.ut * Formula.ut) list =
    (fun (_r, _s, _d, _A, _B) ->
      let _s', _A' =
        (fun (_s', _A') (x, _pt, _D) ->
          M.remove x _s', (fun (a,b,c,d) -> (a,b,(fun c' -> not (c'=_pt)) |>- c,(fun d' -> not (snd d'= snd _D)) |>- d)) _A') |->> ((_s, _A), s_subs) in
      (_r, _s', _d, _A', _B)
    ) |>>| res2 in
  dbg "SUBSTR" "At End:" (List.iter (fun (u,s,d,a,b) -> print_post "SUBSTR" s d a b (Locs.dummy))) res2';
  (res1', res2', _P', ds)

let _Precond fname attr body analyzed currents globals structs s global_post programs =
  let dummy = FAIL in
  try
    let body1 = toT false body in
    dbg "TOT" "Before Translated:\n" pprint body1;
    let body' = COMP (body1, RETURN (Term.zero, Locs.dummy), Locs.dummy) in
    dbg "TOT" "Translated:\n" pprint body';
    let packs = (fname, analyzed, currents, globals, structs, programs) in
    current_function := fname;
    if is_void_pointer attr then
      begin
        pn (fname ^ ": void pointer function is found and is so not analyzed");
        ([], [], body',false_d)
      end
    else
      sub_string_body (s, [], global_post) packs [] body'
  with
    Timeout s -> pn_s "PRECOND" ("TIMEOUT: " ^ s); ([],[],dummy,false_d)
  | StError s -> pn s; ([],[],dummy,false_d)
  | PrecondFails s -> pn_s "PRECOND" (fname ^ "\nMEMORY UNSAFE\n(" ^ s ^ ")"); ([],[],dummy,false_d)
  | NullPointerException s -> p_s "PRECOND" "Memory Unsafe (Null Pointer): "; pn_s "PRECOND" s; ([],[],dummy,false_d)
  | Error -> pn "ERROR"; ([],[],dummy,false_d)
  | MemoryUnsafe -> pn_s "PRECOND" fname ; pn_s "PRECOND" "MEMORY UNSAFE"; ([],[],dummy,false_d)
  | Failure u -> pn_s "PRECOND" fname ; pn_s "PRECOND" ("MEMORY UNSAFE (" ^ u ^ ")"); ([],[],dummy,false_d)
  | e -> pn "Unknown Error"; raise e


let rec in_to_list = function
    COMP (p1, p2, _) -> in_to_list p1 @ in_to_list p2
  | p -> [p]
;;

let execute_global global_declarations store post pack =
  let global_declarations0 = List.rev ((fun a g -> match g with
                                           Global.STATEMENT p -> p::a
                                         | _ -> a
                             ) |->> ([], global_declarations)) in
  let global_declarations' = toT true |>>| global_declarations0 in
  let global_declarations'' = List.concat (in_to_list |>>| global_declarations') in
  
  let rec execute_each (store, post) p' =
    try
       if !Options.to_be_code_printed then
         pprint p';
       let res = (fst3 (precond (store, [], post, F.empty) pack [] p')) in
       if res = [] then
           (store, post)
       else
         let (store', _, post', _, _, _) = List.hd res in
         (store', post')
    with
      StError "Array dimension is not integer" -> (store, post)
    | e ->
       pause "Exception";
       pprint p';
       raise e
  in
  let res = 
    execute_each |->> ((store, post), global_declarations'') in
  res


let _Precond_rec fname attr body analyzed currents globals structs s global_post _X (programs : EL.programs_t) =
  let dummy = FAIL in
  try
    let packs = (fname, analyzed, currents, globals, structs, programs) in

    if is_void_pointer attr then
      ([], [], body, false_d)
    else
      sub_string_body (s, [], global_post) packs _X body
  with
    Timeout s -> pn_s "PRECOND" ("TIMEOUT: " ^ s); ([],[],dummy,false_d)
  | StError s -> pn s; ([],[],dummy,false_d)
  | PrecondFails s -> pn_s "PRECOND" (fname ^ "\nMEMORY UNSAFE\n(" ^ s ^ ")"); ([],[],dummy,false_d)
  | NullPointerException s -> p_s "PRECOND" "Memory Unsafe (Null Pointer): "; pn_s "PRECOND" s; ([],[],dummy,false_d)
  | Error -> pn "ERROR"; ([],[],dummy,false_d)
  | MemoryUnsafe -> pn_s "PRECOND" fname ; pn_s "PRECOND" "MEMORY UNSAFE"; ([],[],dummy,false_d)
  | Failure u -> pn_s "PRECOND" fname ; pn_s "PRECOND" ("MEMORY UNSAFE (" ^ u ^ ")"); ([],[],dummy,false_d)
  | e -> pn "Unknown Error"; raise e

         
(* let filter_global_store global_vars store =
  (fun s k ->
    let v = M.find k store in
    M.add k v s
  ) |->> (M.empty, global_vars) *)

let filter_global_post global_store (a,b,c,d) =
  let vals = snd |>>| (M.bindings global_store) in
  let c' = List.filter (fun (c',_) -> c' |<- vals) c in
  let d' = List.filter (function (_,d'::_) -> d' |<- vals | _ -> raise Error) d in
  (a,b,c',d')
         
let filter_global global_store body =
  let fvs = Block.fv body in
  let globals' : Exp.t list = fst |>>| (M.bindings global_store) in
  let globals'' =
    List.filter (fun g -> List.exists (fun v -> __N g = __N v) fvs) globals' in
  (fvs, globals'')

let get_s0 global_vars param_vars =
  let g0 =
    (fun gs key ->
      let key_bar = _T (Exp.set_bar key) in
      M.add key key_bar gs
    ) |->> (M.empty, global_vars)
  in
  let s0   =
    (fun s fv ->
      let bfv = _T (Exp.set_bar fv) in
      M.add fv bfv s
    ) |->> (g0, param_vars)
  in
  s0

let is_top_level fname =
  fname = !Options.functions
  
let verify m_name fname (attr, params, body) (analyzed: fs) currents global_post global_store (structs : Structure.t V.t) (* (glob_map : (Exp.t list) F.t) *) programs : ((Term.t * i * i) list * d) * t =

  let gt1 = Sys.time () in
  if List.length !Ftools.p_opt > 0 || fname = !Options.functions then
    pn ("\nFunction Name: " ^ fname ^ "");
  pn_s "RES" ""; p_s "RES" m_name; p_s "RES" ": ";
  let params' = (get_var_from_param fname) |>>| params in

  (* let dep_glob = F.find fname glob_map in *)
  let (fvs, globals'') = filter_global global_store body in
  
  let global_store' =
    M.fold (fun key value gs ->
        if is_top_level fname then
          M.add key value gs
        (* else if Exp.is_funcptr key then
          M.add key value gs
        else if Exp.is_ptr key then
          begin
            let key_bar = _T (Exp.set_bar key) in
            M.add key key_bar gs
          end
        else if not (key |<- dep_glob) then
          M.add key value gs *)
        else if key |<- fvs then 
          let key_bar = _T (Exp.set_bar key) in
          M.add key key_bar gs
        else
          gs
      ) global_store M.empty
  in

  (* let global_store'' = filter_global_store globals'' global_store' in *)
  let global_post'' =
    if is_top_level fname then
      filter_global_post global_store' global_post
    else
      empty
  in

  dbg "GLO" "Global Store (s0):" (m_print "GLO") global_store';
  dbg "GLO" "Global Post:" Formula.pprint [global_post''];

  
  let param, arg =
    if !Options.functions <> "" && fname = !Options.functions then
      match !Options.param with
        Some (a, b) -> (a, b)
      | None -> ("-", 0)
    else
      ("-",0)
  in
  let s   =
    (fun s fv ->
      let bfv =
        if __N fv = param then
          _T (_C arg)
        else
          _T (Exp.set_bar fv) in
      M.add fv bfv s) |->> (global_store', params') in
  loop.contents <- 0;
  let t = Sys.time () in
  start_t.contents <- t;
  dbg "GLO" "Initial s:" (m_print "GLO") s;
  let (res, returns, bd, ds) = _Precond fname attr body analyzed currents globals'' structs s global_post'' programs in
  p_s "RES" (fname ^ ": " ^ "TIME: " ^ (string_of_float t) ^ ": "); p_s "RES" "Triple: "; pf_s "RES" pi (List.length returns);
  p_s "RES" "{"; pf_s "RES" (iterS p ";") currents; pn_s "RES" "}";

  if List.length returns = 0 then
    pn_s "TRIPLE" ("No return from " ^ m_name);
  let r = make_spec res returns s fname gt1 ds, bd in
  r
  
  (**
     verify_rec :: 'set of functions' -> 'map of function name to function details' -> 'analyzed functions' -> 'global postcondition' -> 'global store' -> 'list of structures'
   *)

let get_structures func (programs: EL.programs_t) all_structs =
  let (filename, _, _, _) = EL.get_function programs func in
  let gl_structs = V.find "*" all_structs in
  let lc_structs =
    try
      V.find filename all_structs
    with
      Not_found ->
      V.empty
  in
  
  V.fold (fun k v acc ->
      V.add k v acc
    ) gl_structs lc_structs
;;

  
let verify_rec func_grp (programs : EL.programs_t)  all_structs (analyzed: fs) global_post global_store all_structs =

  dbg "REC" "\nThe Function Group:" (iterS pw ",") func_grp;
  let gt1 = Sys.time () in
  
  let v_rec current_function =
    
    let (c_filename, (function_name, params, body)) =
      try
        EL.get_function_details programs  current_function
      with
        _ ->
        pn ("Missing Function: " ^ current_function);
        raise (StError "LIB-1")
    in
  
    let attr = Exp.get_attributes function_name in
    if !Options.to_be_code_printed then
      begin
        pn c_filename;
        Procedure.pprint (__E (current_function,[]), params, body);
        pn "";
      end;
    
    let body1 = toT false body in
    dbg "TOT" "Before Translated:\n" pprint body1;
    let body' = COMP (body1, RETURN (Term.zero, Locs.dummy), Locs.dummy) in
    dbg "TOT" "Translated:\n" pprint body';

    let param_names = ((get_var_from_param "***") |>>| params) in
    let params = _T |>>| param_names in

    
    
    let (_, global_vars) = filter_global global_store body in
    dbg "REC" "Global Vars:" (iterS Exp.pprint ", ") global_vars; 
    let s0 = get_s0 global_vars param_names in

    dbg "REC" "Function initialized:" p current_function;
    
    (current_function, (global_vars), (attr, params, [], body', s0))
  in

  let _X = v_rec |>>| func_grp in

  let phi _Xvec =
    (fun (function_name, global_vars, (attr, params, returns, body, s0)) ->
      dbg "REC" "REC:Starting:" p function_name;
      current_function := function_name;
      let structs = get_structures function_name programs all_structs in
      let (_, returns', _, _) = _Precond_rec function_name attr body analyzed func_grp global_vars structs s0 empty _Xvec programs in
      dbg "REC" "Function computed:" p function_name;
      dbg "REC" "Returns\n" (iterS (fun (r, s, d, a, b) -> p_s "REC" "r:";
                                                           pf_s "REC" Term.pprint r;
                                                           pn_s "REC" "";
                                                           print_post "REC" s d a b (Locs.dummy)
                               ) "\n") returns'; 
      (function_name, global_vars, (attr, params, returns', body, s0))
    ) |>>| _Xvec
  in

  let le ((ri, si, di, ai, bi):r) ((rj, sj, dj, aj, bj):r) : bool =
    let fv_rj = Term.fv rj in
    let fv_range_sj = List.concat (Term.fv |>>| (snd |>>| M.bindings sj)) in
    let fv_aj = Formula.fv aj in
    let fv_bj = Formula.fv bj in
    let fv_j = fv_rj  @@ fv_range_sj @@ fv_aj @@ fv_bj in 
    let fv_g = List.concat (Term.fv |>>| (snd |>>| M.bindings global_store)) in
    let (xs, _) = drop_common fv_j fv_g in
    let s_xs = Exp.toStr |>>| xs in

    let s_ij' = M.merge (fun k i j ->
                    match i, j with
                      Some i', Some j' -> Some (BExp.(i' == j'))
                    | _, _ -> None
                  ) si sj in
    let s_ij = snd |>>| M.bindings s_ij' in
    let di' = BExp.list_to_bexp di in
    let di'' = BExp.complement di' in
    
    let f0 = (s_xs, [BExp.(di'' |. (ri == rj))] @ s_ij @ dj, [], [] ) in
    let b_f0 = VcpVBase.check_sat2  f0 in
    if b_f0 then
      let f1 = Formula.((s_xs, di, [], []) *** ai *** bj)  in
      let f2 = Formula.(aj *** bj) in
      VcpVBase.entail "REC" f1 f2
    else
      false
  in

  let les (_,_,(_,_,_Xi,_,_)) (_,_,(_,_,_Xj,_,_)) =
    List.for_all (fun (xi : r) -> List.exists (fun (xj : r) -> le xi xj) _Xj) _Xi
  in

  let leS _Xs _Ys =
    if List.length _Xs = List.length _Ys then
      let _XYs = List.combine _Xs _Ys in
      List.for_all (fun (_Xi, _Yi) -> les _Xi _Yi) _XYs
    else
      false
  in

  let print_X _X =
    iterS (fun (function_name, global_vars, (attr, params, returns, body, s0)) ->
        print_rets "REC" function_name returns
      ) "\n" _X
  in
  
  let rec do_while _X count =
    dbg "REC" "Count: " pl count;
    dbg "REC" "X: " print_X _X; 
    let _Y = _X in
    let _X' = phi _Y in
    if count > 10 || leS _X' _Y then
      _X'
    else
      do_while _X' (count+1)
  in

  let res = do_while _X 0 in

  let res' = (fun (function_name, global_vars, (attr, params, returns, body, s0)) ->
      
      let r = make_spec [] returns s0 function_name gt1 false_d in
              
      (*      let specifications = (to_spec s0) |>>| returns in *)
      
      (function_name, (attr, params, r, body))
    ) |>>| res in
  (* let specifications = [] in
    (current_function, (attr, t_param_names, (specifications, d_s), bd))
   *)
  res'

