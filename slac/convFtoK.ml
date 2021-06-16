open Tools
open Slsyntax
open Interval
open Smtsyntax
open Sltosmt
open Smttoz3
   
module X = Ftools
module F = VcpBase
module T = SHterm
module P = SHpure
         
module Fexp = F.Exp
module Fop = F.Op
module Ftm = F.Term
module Fbex = F.BExp
module Flocs = F.Locs
module Fptr = F.Pointer
module Fblock = VcpTranslate.Block
module Fglobal = VcpTranslate.Global
module Fstructure = VcpTranslate.Structure
module Fprogram = VcpTranslate.Program
module Fprocedure = VcpTranslate.Procedure
module Fmodule = VcpAllC

module K = Csyntax
module Kexp = Csyntax.Exp
module Kbexp = Csyntax.Bexp
module Kinit = Csyntax.Init
module Kdecl = Csyntax.Decl
module Kstmt = Csyntax.Stmt
module KtopDecl = Csyntax.TopDecl
module Kprogram = Csyntax.Program
module Kstructure = Csyntax.Structure
module Kmodule = Csyntax.Module
module Klocs = Csyntax.Locs
module MyFp = Fp3
module MyFpsyntax = Fpsyntax3          
module FPsh = MyFpsyntax.StoreHeap
module FpPos = MyFp.FpPos
module FPstate = MyFpsyntax.State
module FPval = MyFpsyntax.Val
               
(* overwriting of print_... in tools.ml *)
let print_warn tag mes = Ftools.pf_s "FPAwarn" print_endline ("[W " ^ tag ^ "] " ^ mes)
  
let print_error tag mes = Ftools.pf_s "FPAwarn" print_endline ("[E " ^ tag ^ "] " ^ mes)

let print_mes tag mes = Ftools.pf_s "FPAwarn" print_endline ("[_ " ^ tag ^ "] " ^ mes)
               
module ConvFtoK = struct

  let ignored x = T.Var ("ignored_"^x, []) 

  let rec of_attr (fattr : Fexp.attr) =
    match fattr with
    | Fexp.PTR -> T.PTR
    | Fexp.HAT -> T.HAT
    | Fexp.BAR -> T.BAR
    | Fexp.DOT -> T.DOT
    | Fexp.TILDE -> T.TILDE
    | Fexp.CHECK -> T.CHECK
    | Fexp.STRUCT str -> T.STRUCT str
    | Fexp.STATIC -> T.EXQ (* mostly dummy, will not be used *)
    | Fexp.EXQ -> T.EXQ (* will not be used *)
    | Fexp.ARRAY ee -> T.ARRAY [1] (* will not be used *)
    | Fexp.PARAM -> T.PARAM (* will not be used *)
    | Fexp.PTRPTR -> T.PTRPTR (* will not be used *)
    | Fexp.GLOBAL -> T.GLOBAL (* will not be used *)
    | Fexp.EXTERN -> T.EXTERN (* will not be used *)
    | Fexp.FUNCPTR _ -> T.PROTO
    | Fexp.FUNC _ -> T.FUNC
    | Fexp.NESTED -> T.NESTED (* will not be used *)
    | Fexp.QUESTION -> T.QUESTION
    | Fexp.DOTDOT -> T.DOTDOT
    | Fexp.ACUTE -> T.ACUTE
    | Fexp.SIMPLE n -> T.SIMPLE n
    | Fexp.INDIRECT -> T.INDIRECT

  and of_exp (e : Fexp.t) =
    match e with
        (*
	  | Fexp.ADDR(Fexp.VAR(v,_)) -> T.Var ("&" ^ v, [])
      | Fexp.ADDR x -> X.pw "Unsupported Var(ADDR) "; Fexp.pprint e; X.pn ""; of_exp x 
         *)
    | Fexp.REF x -> X.pw "Unsupported Var(REF) "; Fexp.pprint e; X.pn ""; of_exp x
    | Fexp.NEG x -> X.pw "Unsupported Var(NEG) "; Fexp.pprint e; X.pn ""; of_exp x
	| Fexp.ADDR t -> (* &t *)
       let t' = of_exp t in
       T.Fcall ("#ADDR", [t'])
    | Fexp.NOTHING -> T.Int 0
    | Fexp.NEGINF -> T.Int (min_int)
    | Fexp.POSINF -> T.Int (max_int)
    | Fexp.UNDEF  -> T.Var ("?(undef)", [])
    | Fexp.STRING _ -> T.Var ("?(string)", [])
    | Fexp.ARROW (t,f) ->
       let t' = of_exp t in
       let f' = T.Var (f, []) in (* field name *)
       T.Fcall ("#ARROW", [t';f'])
    | Fexp.VAR (v,attrs) -> (* ("x",[HAT;PTR]) becomes "x@hat@ptr" *)       
       let attrs' = List.map of_attr attrs in       
       T.Var (v, attrs')
    | Fexp.CONST n -> T.Int n
    | Fexp.FLOAT f -> T.Int (int_of_float f)
    | Fexp.LBL (label,t) ->
       let label' = T.Var (label, []) in (* label name *)
       let t' = of_exp t in
       T.Fcall ("#LBL", [label';t'])
    | Fexp.FCALL (s,tt) ->
       let tt' = List.map of_exp tt in
       T.Fcall (s,tt')
    | Fexp.BINOP(e1,op,e2) ->
	   let t1 = of_exp e1 in
	   let t2 = of_exp e2 in
	   begin
	     match op with
	     | Fop.ADD -> T.Add [t1;t2]
         | Fop.SUB -> T.Sub [t1;t2]
         | Fop.MUL -> T.Mul (t1,t2)
         | Fop.DIV -> T.Div (t1,t2)
         | Fop.MOD -> T.Mod (t1,t2)
         | Fop.EQ -> ignored "eq"
         | Fop.NE -> ignored "ne"
         | Fop.LE -> ignored "le"
         | Fop.OR -> ignored "or"
         | Fop.AND -> ignored "and"
         | Fop.DUMMY -> ignored "dummy"
         | Fop.SHL -> T.Shl (t1,t2)
         | Fop.SHR -> T.Shr (t1,t2)
         | Fop.BOR -> T.Bor (t1,t2)
         | Fop.BAND -> T.Band (t1,t2)
         | Fop.MAPSTO -> ignored "mapsto"
         | Fop.MIN -> ignored "min"
         | Fop.MAX -> ignored "max"
         | Fop.XOR -> ignored "xor"
	   end
    | Fexp.INDICES ee ->            (* to fix *)
       let tt = List.map of_exp ee in
       List.hd tt 
    | Fexp.OFFSET (strName,e0) ->
       let t0 = of_exp e0 in
       T.Offset(strName,t0)
    | Fexp.SIZEOF (tp) -> T.Int 0 (* ignored *)

  let rec of_term t =
    match t with
    | Ftm.NULL -> T.Int 0
    | Ftm.EXP e -> of_exp e
      (*    | Ftm.FCALL (s, _) -> of_exp (Fexp.VAR (s ^ "-func",[Fexp.HAT])) *)

  let rec of_bexp (bx : F.BExp.t) : SHpure.t list =
    match bx with
    | Fbex.UNIT (t1,op,t2) ->
       let t1' = of_term t1 in
       let t2' = of_term t2 in
       begin
	     match op with
	     | Fop.ADD -> []
	     | Fop.SUB -> []
	     | Fop.MUL -> []
	     | Fop.DIV -> []
	     | Fop.MOD -> []
	     | Fop.EQ ->  [ P.Atom (P.Eq, [t1'; t2']) ]
	     | Fop.NE ->  [ P.Atom (P.Neq,[t1'; t2']) ]
	     | Fop.LE ->  [ P.Atom (P.Lt, [t1'; t2']) ]
	     | Fop.OR -> []
		 | Fop.AND -> []
		 | Fop.DUMMY -> []
		 | Fop.SHL -> []
		 | Fop.SHR -> []
		 | Fop.BOR -> []
		 | Fop.BAND -> []
		 | Fop.MAPSTO -> []
		 | Fop.MAX -> []
		 | Fop.MIN -> []
         | Fop.XOR -> []
       end
    | Fbex.OP(Fbex.UNIT(bx1, Fop.EQ, bx2), Fop.OR, Fbex.UNIT(bx3, Fop.LE, bx4)) when bx1=bx4 && bx2=bx3
      -> [ P.Atom (P.Le, [of_term bx3; of_term bx4]) ]
    | Fbex.OP(Fbex.UNIT(bx1, Fop.EQ, bx2), Fop.OR, Fbex.UNIT(bx3, Fop.LE, bx4)) when bx1=bx3 && bx2=bx4
      -> [ P.Atom (P.Le, [of_term bx3; of_term bx4]) ]
    | Fbex.OP(Fbex.UNIT(bx1, Fop.LE, bx2), Fop.OR, Fbex.UNIT(bx3, Fop.EQ, bx4)) when bx1=bx3 && bx2=bx4
      -> [ P.Atom (P.Le, [of_term bx3; of_term bx4]) ]
    | Fbex.OP(Fbex.UNIT(bx1, Fop.LE, bx2), Fop.OR, Fbex.UNIT(bx3, Fop.EQ, bx4)) when bx1=bx4 && bx2=bx3
      -> [ P.Atom (P.Le, [of_term bx3; of_term bx4]) ]
    | Fbex.OP(bx1,op,bx2) ->
       let pp1 = of_bexp bx1 in
       let pp2 = of_bexp bx2 in
       begin
	     match op with
	     | Fop.ADD -> []
	     | Fop.SUB -> []
	     | Fop.MUL -> []
	     | Fop.DIV -> []
	     | Fop.MOD -> []
	     | Fop.EQ ->  []
	     | Fop.NE ->  []
	     | Fop.LE ->  []
	     | Fop.OR ->
            let p1 = P.And pp1 in
            let p2 = P.And pp2 in
            [ (p1 |.| p2) ]
		 | Fop.AND -> pp1 @ pp2
		 | Fop.DUMMY -> []
		 | Fop.SHL -> []
		 | Fop.SHR -> []
		 | Fop.BOR -> (print_endline "\nBOR!!!"; [])
		 | Fop.BAND -> (print_endline "\nBAND!!!"; [])
		 | Fop.MAPSTO -> []
		 | Fop.MAX -> []
		 | Fop.MIN -> []
         | Fop.XOR -> (print_endline "\nXOR!!!"; [])
       end
    | Fbex.BLOCK(_,_) -> []
    | Fbex.NOTHING -> []
    | Fbex.LBL(_,_) -> []
      
  let of_bexpL bxl : SHpure.t =
    let pure = P.And (List.flatten (List.map of_bexp bxl)) in
    pure
    
  let of_pointer (pt : F.Pointer.t) : SHspatExp.t =
    let (t,fts) = pt in
	let t' = of_term t in
    let ts' = List.map (fun (f,t) -> (f,of_term t)) fts in
    SHspatExp.Pto(t',ts')

  let of_predicate (pr : F.Predicate.t) : SHspatExp.t = 
    let (id,tms) = pr in
    match id with
    | "Array" -> 
      let tt = List.map of_term tms in
      let t0 = try List.nth tt 0 with _ -> raise (X.StError "Nth: convFtoK-1") in
      let t1 = try List.nth tt 1 with _ -> raise (X.StError "Nth: convFtoK-1") in
      S.Arr(t0,t1)
    | "Stringpart" -> 
      let tt = List.map of_term tms in
      let t0 = try List.nth tt 0 with _ -> raise (X.StError "Nth: convFtoK-1") in
      let t1 = try List.nth tt 1 with _ -> raise (X.StError "Nth: convFtoK-1") in
      S.Str(t0,t1)
    | _ -> raise (X.StError "Nth: convFtoK-1")

  let of_oneformula fml : SH.t =
    let (vv,bexps, (ptrs:F.Pointer.t list),preds) = fml in
    let pure = of_bexpL bexps in
    let spat1 = List.map of_pointer ptrs in
    let spat2 = List.map of_predicate preds in
    let sh = (vv,pure,spat1@spat2) in
    sh

  let get_pto_len fm =
    let (_,_,ptrs,_) = fm in
    let args = List.map snd ptrs in
    if args = [] then 0 else List.length (List.hd args)

  let of_entl (f_ent : F.Formula.t * F.Formula.t) : Entl.t list =
    let (fml1,fml2) = f_ent in    
    let shL = List.map of_oneformula (fml1) in
    let shR = List.map of_oneformula (fml2) in
    List.map (fun s -> (s,shR)) shL

  let of_entlL f_entL : PS.t =
    List.concat (List.map of_entl f_entL)

  (* segment is a list of intervals (= pair of terms) *)
  let of_segment f_seg : Seg.t =
    L.map (fun (t1,t2) -> (of_term t1,of_term t2)) f_seg
        
end
;;

(* some short cuts *)
let fnum n = Ftm.EXP (Fexp.CONST n);;

let fzero = fnum 0;;

let ( =..= ) tm1 tm2 = Fbex.UNIT (tm1,Fop.EQ,tm2);;

let ( <..> ) tm1 tm2 = Fbex.UNIT (tm1,Fop.NE,tm2);;

let ( |..| ) bx1 bx2 = Fbex.OP (bx1,Fop.OR,bx2);;

let ( &..& ) bx1 bx2 = Fbex.OP (bx1,Fop.AND,bx2);;

let ( <..< ) tm1 tm2 = Fbex.UNIT (tm1,Fop.LE,tm2);;

let ( <..= ) tm1 tm2 = (tm1 <..< tm2) |..| (tm1 =..= tm2);;



(* convertor from Faisal's C to Kimura's C *)
module ConvFCtoKC = struct

  let _exfunL = ref []

  let of_op fop =
    match fop with
    | Fop.ADD -> Kexp.Add
    | Fop.SUB -> Kexp.Sub
    | Fop.MUL -> Kexp.Mul
    | Fop.DIV -> Kexp.Div
    | Fop.MOD -> Kexp.Mod
    | Fop.SHL -> Kexp.Shl
    | Fop.SHR -> Kexp.Shr
    | Fop.BOR -> Kexp.Bor
    | Fop.BAND -> Kexp.Band
    | Fop.XOR-> Kexp.Bxor
    | Fop.EQ -> failwith "convFCtoKC.of_op: unsupported input (EQ)"
    | Fop.NE -> failwith "convFCtoKC.of_op: unsupported input (NE)"
    | Fop.LE -> failwith "convFCtoKC.of_op: unsupported input (LE)"
    | Fop.OR -> failwith "convFCtoKC.of_op: unsupported input (OR)"
    | Fop.AND -> failwith "convFCtoKC.of_op: unsupported input (AND)"
    | Fop.DUMMY -> failwith "convFCtoKC.of_op: unsupported input (DUMMY)"
    | Fop.MAPSTO -> failwith "convFCtoKC.of_op: unsupported input (MAPSTO)"
    | Fop.MIN-> failwith "convFCtoKC.of_op: unsupported input (MIN)"
    | Fop.MAX-> failwith "convFCtoKC.of_op: unsupported input (MAX)"
              
  let rec of_attr (fattr : Fexp.attr) : Kexp.tp =
    match fattr with
    | Fexp.PTR -> [Kexp.PTR]
    | Fexp.FUNCPTR (tpRet,tpPrm) ->
       let tpRet' = of_type tpRet in
       let tpPrm' = of_type tpPrm in
       [Kexp.FUNCPTR (tpRet',tpPrm')]
    | Fexp.FUNC (tpRet,tpPrm) ->
       let tpRet' = of_type tpRet in
       let tpPrm' = of_type tpPrm in
       [Kexp.FUNC (tpRet',tpPrm')]
    | Fexp.STRUCT name -> [Kexp.STRUCT name]
    | Fexp.ARRAY ee -> [Kexp.ARRAY (List.map of_exp ee)]
    | Fexp.PTRPTR -> [Kexp.PTR;Kexp.PTR]
    | Fexp.SIMPLE n -> [Kexp.SIMPLE n]                   
    | Fexp.NESTED -> [Kexp.OTHER "NESTED"]                   
    | Fexp.GLOBAL -> [Kexp.OTHER "GLOBAL"]
    | Fexp.EXTERN -> [Kexp.OTHER "EXTERN"]
    | Fexp.STATIC -> [Kexp.OTHER "STATIC"]
    | Fexp.EXQ -> [Kexp.OTHER "EXQ"]
    | Fexp.PARAM -> [Kexp.OTHER "PARAM"]
    | Fexp.HAT -> [Kexp.OTHER "HAT"]
    | Fexp.BAR -> [Kexp.OTHER "BAR"]
    | Fexp.TILDE -> [Kexp.OTHER "TILDE"]
    | Fexp.CHECK -> [Kexp.OTHER "CHECK"]
    | Fexp.DOT -> [Kexp.OTHER "DOT"]
    | Fexp.ACUTE -> [Kexp.OTHER "ACUTE"]
    | Fexp.DOTDOT -> [Kexp.OTHER "DOTDOT"]
    | Fexp.QUESTION -> [Kexp.OTHER "QUESTION"]
    | Fexp.INDIRECT -> [Kexp.OTHER "INDIRECT"]
  (* types *)                     
  and of_type (ftp : Fexp.attr list) : Kexp.tp =
    let tpL = List.map of_attr ftp in
    unionL tpL
  (* vars *)
  and of_var (fvar : Fexp.var_t) : Kexp.tp * Kexp.lval =
    let (v,ftp) = fvar in
    let tp = of_type ftp in
    let lval = Kexp.Var (v,tp) in
    (tp,lval)
  (* lvals *)
  and of_var_to_lval (fvar : Fexp.var_t) : Kexp.lval =
    let (v,ftp) = fvar in
    let tp = of_type ftp in
    let lval = Kexp.Var (v,tp) in
    lval
  (* expressions *)
  and of_exp (fexp : Fexp.t) : Kexp.t =
    match fexp with
    | Fexp.UNDEF -> Kexp.Unknown
	| Fexp.VAR fvar ->
       let lval = of_exp_to_lval fexp in
       Kexp.Lval lval
	| Fexp.CONST n -> Kexp.Int n
    | Fexp.BINOP (e,Fop.ADD,Fexp.INDICES ee) ->
    (* BINOP(a,[x;y]) --> a[x][y] *)
       let aLval = of_exp_to_lval e in
       let tt = List.map of_exp ee in
       Kexp.Lval (Kexp.Array (aLval,tt))
	| Fexp.BINOP (fexp1,fop,fexp2) ->
       let op = try
           of_op fop
         with
           e -> Fexp.pprint fexp; print_string' "\n"; raise e
       in
       let e1 = of_exp fexp1 in
       let e2 = of_exp fexp2 in
       Kexp.Op(op,e1,e2)
    | Fexp.LBL (label,fexp1) ->
       let e1 = of_exp fexp1 in
       Kexp.Lbl (e1,label)
    | Fexp.FCALL (fname,fexpL) ->
       if List.mem fname !_exfunL
       then
         let e = Kexp.Lval (Kexp.Var ("<unsupported>",[])) in
         Kexp.Fcall (fname,[e])
       else
         let eL = List.map of_exp fexpL in
         Kexp.Fcall (fname,eL)
    | Fexp.ADDR fexp1 ->
       let lval = of_exp_to_lval fexp1 in
       Kexp.Addr lval
    | Fexp.ARROW _ ->
       let lval = of_exp_to_lval fexp in
       Kexp.Lval lval
    | Fexp.REF _ ->
       let lval = of_exp_to_lval fexp in
       Kexp.Lval lval       
    | Fexp.NEG _ -> Fexp.pprint fexp; failwith "convFCtoKC.of_exp: unsupported input (NEG)"
    | Fexp.NOTHING ->
       Kexp.Lval (Kexp.Var ("<nothing>",[]))
    | Fexp.NEGINF -> Fexp.pprint fexp; failwith "convFCtoKC.of_exp: unsupported input (NEGINF)"
    | Fexp.POSINF -> Fexp.pprint fexp; failwith "convFCtoKC.of_exp: unsupported input (POSINF)"
	| Fexp.FLOAT _ -> Fexp.pprint fexp; failwith "convFCtoKC.of_exp: unsupported input (FLOAT)"
    | Fexp.STRING s -> Kexp.String s
    | Fexp.INDICES ee ->
       List.iter Fexp.pprint ee;
       failwith "convFCtoKC.of_exp: This branch should not come"
    | Fexp.OFFSET (strName,e) ->
       let t = of_exp e in
       Kexp.Offset (strName,t)
    | Fexp.SIZEOF tp -> Kexp.Int 0 (* ignored *)
              
  and of_exp_to_lval fexp =
    match fexp with
	| Fexp.VAR fvar ->
       of_var_to_lval fvar
    | Fexp.ARROW (Fexp.VAR fvar,field) ->
       let (tp,_) = of_var fvar in
       let e1 = of_exp (Fexp.VAR fvar) in
       Kexp.Arrow (e1,tp,field)
    | Fexp.ARROW (fexp1,field) ->
       let e1 = of_exp fexp1 in
       Kexp.Arrow (e1,[],field)
    | Fexp.REF fexp1 ->
       let e1 = of_exp fexp1 in
       Kexp.Ptr e1
    | Fexp.BINOP (e,Fop.ADD,Fexp.INDICES ee) ->
       (* BINOP(a,ADD,INDICES[x;y;z]) --> a[x][y][z] *)
       let aLval = of_exp_to_lval e in
       let tt = List.map of_exp ee in
       Kexp.Array (aLval,tt)
    | Fexp.BINOP (e,Fop.ADD,e1) ->
       (* BINOP(a,ADD,x) --> a[x] *)
       let aLval = of_exp_to_lval e in
       let t = of_exp e1 in
       Kexp.Array (aLval,[t])
    | _ ->
       print_endline "convFCtoKC.of_exp_to_lval: Unexpected expression-3";
       Fexp.print fexp; print_endline "";
       failwith ""

  let get_rettype_of_exp fexp =
    match Fexp.head "" fexp with
	| Fexp.VAR (fname,[Fexp.FUNCPTR (tpRet,_)]) -> of_type tpRet
	| Fexp.VAR (fname,[Fexp.FUNC (tpRet,_)]) -> of_type tpRet                                                 
	| _ -> [] (* dummy *)
         
  let get_type_of_exp fexp = 
    match Fexp.head "" fexp with
	| Fexp.VAR (fname,ftp) -> of_type ftp
	| _ -> [] (* dummy *)

  let of_exp_to_lval_tp fexp =
    match fexp with
	| Fexp.VAR fvar -> 
       let (v,ftp) = fvar in
       let tp = of_type ftp in
       let lval = Kexp.Var (v,tp) in
       (lval,tp)
    | _ ->
       Fexp.pprint fexp;
       failwith "\nconvFCtoKC.of_exp_to_lvar_tp: unsupported input"
       
  let of_term (fterm : Ftm.t) : Kexp.t =
    match fterm with
	| Ftm.EXP fexp ->
       begin
         try
           of_exp fexp
         with
           e ->
           X.pn_s "EXCEPK" ""; X.pf_s "EXCEPK" Ftm.pprint fterm; X.pn_s "EXCEPK" " : Exceptional Term"; raise e 
       end
	| Ftm.NULL -> Kexp.z (* zero *)

  let get_type_of_term (fterm : Ftm.t) =
    match fterm with
	| Ftm.EXP fexp -> get_type_of_exp fexp
	| Ftm.NULL -> []

  (* This returns (tpRet,tpPrm) of a function fterm *)
  let get_types_of_funterm (fterm : Ftm.t) : Kexp.tp * Kexp.tp =
    let tp = get_type_of_term fterm in
    Kexp.getFunctionTp tp

  let checkFP_fterm (fterm : Ftm.t) =
    let tp = get_type_of_term fterm in
    Kexp.isFpType tp
    
  let of_term_to_lval (fterm : Ftm.t) : Kexp.lval =
    match fterm with
	  | Ftm.EXP fexp ->
       begin
         try
           of_exp_to_lval fexp
         with
           e -> X.pn_s "EXCEPK" ""; X.pf_s "EXCEPK" Ftm.pprint fterm; X.pn_s "EXCEPK" " : Exceptional Term"; raise e 
       end
	| Ftm.NULL -> failwith "convFCtoKC.of_term_to_lval: unsupported input (NULL)"
    
  let rec of_bexp (fbex : Fbex.t) : Kbexp.t =
    match fbex with
    | Fbex.OP (Fbex.UNIT(t1, Fop.LE, t2), Fop.OR, Fbex.UNIT(t3, Fop.EQ, t4)) when t1=t3 && t2=t4 ->
       let e1 = of_term t1 in
       let e2 = of_term t2 in
       Kbexp.Le (e1,e2)
    | Fbex.OP (Fbex.UNIT(t1, Fop.EQ, t2), Fop.OR, Fbex.UNIT(t3, Fop.LE, t4)) when t1=t3 && t2=t4 ->
       let e1 = of_term t1 in
       let e2 = of_term t2 in
       Kbexp.Le (e1,e2)
    | Fbex.OP (fbex1, fop, fbex2) ->
       let bex1 = of_bexp fbex1 in
       let bex2 = of_bexp fbex2 in
       begin
         match fop with
         | Fop.OR -> Kbexp.Or (bex1,bex2)
         | Fop.AND -> Kbexp.And (bex1,bex2)
         | _ -> failwith "convFCtoKC.of_op: unsupported boolean operator"
       end
    | Fbex.UNIT (fterm1,fop,fterm2) ->
       let e1 = of_term fterm1 in
       let e2 = of_term fterm2 in
       begin
         match fop with
         | Fop.EQ -> Kbexp.Eq (e1,e2)
         | Fop.NE -> Kbexp.Neq (e1,e2)
         | Fop.LE -> Kbexp.Lt (e1,e2)
         | _ -> failwith "convFCtoKC.of_op: unsupported input (UNIT)"
       end
	| Fbex.BLOCK (fvar,fterm) -> failwith "convFCtoKC.of_op: unsupported input (BLOCK)"
    | Fbex.LBL (label,fbex1) ->
       let bex1 = of_bexp fbex1 in
       Kbexp.Lbl (bex1,label)
	| Fbex.NOTHING -> failwith "convFCtoKC.of_bexp: unsupported input (NOTHING)"

  let rec of_init (finit : Fblock.init) : Kinit.t =
    match finit with
    | Fblock.INIT_E -> Kinit.None
    | Fblock.INIT_S e -> Kinit.S (of_term e)
    | Fblock.INIT_M finitL -> Kinit.M (List.map of_init finitL)
                    
  let rec of_block strV (fblk : Fblock.t) : Kstmt.t list =    
    match fblk with
    | Fblock.SKIP ->
       [Kstmt.Skip]
    | Fblock.DECL (fexp,ftermL_len,finit,fblk1,loc) ->
       let (lval,tp) = of_exp_to_lval_tp fexp in
       let kinit = of_init finit in
       let decl = Kdecl.Decl (tp,lval,kinit) in
       let stmtDecl = Kstmt.Decl (decl,loc) in
       let stmtL = of_block strV fblk1 in
       stmtDecl :: stmtL
    | Fblock.ASSERT (fml,fblk1,loc) ->
       (*
       let stmt = Kstmt.Unknown loc in
       let stmtL = of_block strV fblk1 in
       stmt :: stmtL
        *)
       let stmtL = of_block strV fblk1 in (* optimization for funcp *)
       stmtL
    | Fblock.ASSIGN (var,fterm,fblk1,loc) ->
       let (v,attrL) = Fexp.var var in
       let tp = of_type attrL in
       begin
         match Kexp.isFpType tp with (* optimization for funcp *)
         | true ->
            let lval = Kexp.Var (v,tp) in
            let e = of_term fterm in
            let stmt = Kstmt.Asgn (lval,e,loc) in
            let stmtL = of_block strV fblk1 in
            stmt :: stmtL
         | false ->
            let stmtL = of_block strV fblk1 in
            stmtL
       end
    (* WHILE(cond,string_cond,body,fml,rest,loc) *)
    | Fblock.WHILE (fbexp,fbexpL,fblkBody,_,fblk1,loc) ->
       (*
       let bexp = try of_bexp fbexp with e -> raise e in
       let bexpL = try List.map of_bexp fbexpL  with e -> raise e in
        *)
       let bexp = Kbexp.true_ in (* optimization for funcp *)
       let bexpL = [Kbexp.true_] in
       let stmtBody = Kstmt.mkBlock (of_block strV fblkBody) loc in
       let stmt = Kstmt.While (bexp,bexpL,stmtBody,loc) in
       let stmtL = of_block strV fblk1 in
       stmt :: stmtL
    | Fblock.IF (fbexp,fblkThen,fblkElse,fblk1,loc) ->
       (*
       let bexp = try of_bexp fbexp with e -> raise e in
        *)
       let bexp = Kbexp.true_ in (* optimization for funcp *)
       let ssThen = of_block strV fblkThen in
       let ssElse = of_block strV fblkElse in
       let locThen = if ssThen <> [] then Kstmt.getloc (List.hd ssThen) else loc in
       let locElse = if ssElse <> [] then Kstmt.getloc (List.hd ssElse) else loc in
       let stmtThen = Kstmt.mkBlock ssThen locThen in
       let stmtElse = Kstmt.mkBlock ssElse locElse in
       let stmt = Kstmt.If (bexp,stmtThen,stmtElse,loc) in
       let stmtL = of_block strV fblk1 in
       stmt :: stmtL
    (* MUTATION (p,"*",e,rest,_) is "*p = e" *)
    (* MUTATION (p, f ,e,rest,_) is "p->f = e" *)
    | Fblock.MUTATION (fterm1,field,fterm2,fblk1,loc) ->
       let tp = get_type_of_term fterm1 in
       let lval =
         let e1 = try of_term fterm1 with e -> raise e in
         if field = "*"
         then Kexp.Ptr e1
         else Kexp.Arrow (e1,tp,field)
       in
       let e = of_term fterm2 in
       let stmt = Kstmt.Asgn (lval,e,loc) in
       let stmtL = of_block strV fblk1 in
       stmt :: stmtL
    (* LOOKUP (l,e2,"*",rest,_) is "l = *e" *)
    (* LOOKUP (l,e2, f ,rest,_) is "l = e->f" *)
    | Fblock.LOOKUP (fexp,fterm,field,fblk1,loc) ->
       begin
         match Kexp.isFpType (get_type_of_exp fexp) with (* optimization for funcp *)
         | true -> 
            let tp = get_type_of_term fterm in
            let lval = of_exp_to_lval fexp in
            let e =
              let e1 = of_term fterm in
              if field = "*"
              then Kexp.Lval (Kexp.Ptr e1)
              else Kexp.Lval (Kexp.Arrow (e1,tp,field))
            in
            let stmt = Kstmt.Asgn (lval,e,loc) in
            let stmtL = of_block strV fblk1 in
            stmt :: stmtL
         | false ->
            let stmtL = of_block strV fblk1 in
            stmtL
       end
       (*
       let tp = get_type_of_term fterm in
       let lval = of_exp_to_lval fexp in
       let e =
         let e1 = of_term fterm in
         if field = "*"
         then Kexp.Lval (Kexp.Ptr e1)
         else Kexp.Lval (Kexp.Arrow (e1,tp,field))
       in
       let stmt = Kstmt.Asgn (lval,e,loc) in
       let stmtL = of_block strV fblk1 in
       stmt :: stmtL
        *)
    (* PROCCALL-1: fp call *)
    (* The return value of "f(..)" is received by "$ret" in Faisal's data *)
    | Fblock.PROCCALL (fterm,ftermL,pos,fblk1,loc) when checkFP_fterm fterm ->
       let fp = Ftm.toStr fterm in
       let (tpRet,tpPrm) = get_types_of_funterm fterm in
       let ee = List.map of_term ftermL in
       let stmt = Kstmt.FPcall (fp,pos,ee,tpRet,tpPrm,loc) in
       let stmtL = of_block strV fblk1 in
       stmt :: stmtL
    (* PROCCALL-2: normal function call *)
    | Fblock.PROCCALL (fterm,ftermL,_,fblk1,loc) -> 
       let fname = Ftm.toStr fterm in
       let (tpRet,tpPrm) = get_types_of_funterm fterm in
       if List.mem fname !_exfunL
       then
         let e = Kexp.Lval (Kexp.Var ("unsupported",[])) in
         let stmt = Kstmt.Fcall (fname,[e],tpRet,tpPrm,loc) in
         let stmtL = of_block strV fblk1 in
         stmt :: stmtL
       else
         let ee = List.map of_term ftermL in
         let stmt = Kstmt.Fcall(fname,ee,tpRet,tpPrm,loc) in
         let stmtL = of_block strV fblk1 in
         stmt :: stmtL
    (* MALLOC(var,name,exp_termL,rest,loc) is var = malloc(sizeof(name)*length) *)
    (* Note: name = "int", "char", .., "A", where "A" means struct A *)
    (* var: generated variable like "#_1" *)
    | Fblock.MALLOC (fexp,fterm_length,fblk1,loc) ->
       (*
       let tp = [] in (* ignored *)
       begin
         match of_exp_to_lval fexp with
         | Kexp.Var (v,_) ->
            let e_length = of_exp fterm_length in
            let stmt = Kstmt.Malloc (v,tp,e_length,loc) in
            let stmtL = of_block strV fblk1 in
            stmt :: stmtL
         | lval ->
            K.print_warn loc "convFCtoKC: MALLOC (unexpected fvar)";
            X.dbg "EXCEPK" "convFCtoKC: MALLOC (unexpected fvar)\n" (Fblock.pprint 0) fblk;
            let v = Kexp.to_string_lval lval in (* dummy variable *)
            let e_length = of_exp fterm_length in
            let stmt = Kstmt.Malloc (v,tp,e_length,loc) in
            let stmtL = of_block strV fblk1 in
            stmt :: stmtL
       end
        *)
       let stmtL = of_block strV fblk1 in (* optimization for funcp *)
       stmtL
    (* DISPOSE : it's translated into "free" *)       
    | Fblock.DISPOSE (fterm,fblk1,loc) ->
       (*
       let e = of_term fterm in
       let stmt = Kstmt.Free (e,loc) in
       let stmtL = of_block strV fblk1 in
       stmt :: stmtL
        *)
       let stmtL = of_block strV fblk1 in (* optimization for funcp *)
       stmtL
    | Fblock.BLOCK (f_blockA,f_block1,loc) ->
       let stmt = Kstmt.mkBlock (of_block strV f_blockA) loc in
       let stmtL = of_block strV f_block1 in
       stmt :: stmtL
    | Fblock.RETURN (f_term,f_block1,loc) ->
       let e = of_term f_term in
       let stmt = Kstmt.Return (e,loc) in
       let stmtL = of_block strV f_block1 in
       stmt :: stmtL
    | Fblock.LABEL (label,el,f_block1,loc) ->
       (*
       let stmt = Kstmt.Lbl (label,el,loc) in
       let stmtL = of_block strV f_block1 in
       stmt :: stmtL
        *)
       let stmtL = of_block strV f_block1 in (* optimization for funcp *)
       stmtL
    | Fblock.BREAK (f_block1,loc) ->
       (*
       let stmt = Kstmt.Break loc in
       let stmtL = of_block strV f_block1 in
       stmt :: stmtL
        *)
       let stmtL = of_block strV f_block1 in (* optimization for funcp *)
       stmtL
    | Fblock.CONTINUE (f_block1,loc) ->
       (*
       let stmt = Kstmt.Continue loc in
       let stmtL = of_block strV f_block1 in
       stmt :: stmtL
        *)
       let stmtL = of_block strV f_block1 in (* optimization for funcp *)
       stmtL
    | Fblock.FAIL ->
       [Kstmt.Fail Klocs.dummy]
    (* SARRAY: currently just ignored *)
    | Fblock.SARRAY (fvar,fterm,fexpTermL,fblk1,_) ->
       failwith "convFCtoKC.of_block: Unsupported input (SARRAY)"
    (* CONS: currently just ignored *)
    | Fblock.CONS (fexp,fvarTermL,fblk1,_) ->
       failwith "convFCtoKC.of_block: Unsupported input (CONS)"
    (* MAPS: currently just ignored *)
    | Fblock.MAPS (fvar1,fvar2,fblk1,_) ->
       failwith "convFCtoKC.of_block: Unsupported input (MAPS)"
    (* PARALLEL: currently just ignored *)
    | Fblock.PARALLEL (_,_,fblk1,_) ->
       failwith "convFCtoKC.of_block: Unsupported input (PARALLEL)"
     
  let of_structure (structure: Fstructure.t) : Kstructure.t =
    (* Faisal's one
        type t = string * (Var.t * Term.t) list * (bytes * Var.t list) option
        the last clause is IGNORED
     *)
    let f fvar = 
      let (v,attrL) = fvar in
      let tp = of_type attrL in
      (v,tp)
    in
    let (name,varTermL,_) = structure in
    let bodyL = List.map (function (Fexp.VAR fvar, _) -> f fvar | _ -> raise (Ftools.StError "Not a variable")) varTermL in
    (name,bodyL)

  let rec of_global strV (g : Fglobal.t) : KtopDecl.t =
    (* For handling parameters of a func.def *)
    let from_fblk_to_decl fblk = 
      match fblk with
      | Fblock.DECL (fexp,_,_,_,_) ->
         let (lval,tp) = of_exp_to_lval_tp fexp in
         (tp,lval)
      | _ -> failwith "convFCtoKC.of_global"
    in
    match g with
    | Fglobal.NA ->
       KtopDecl.NA Klocs.dummy
    | Fglobal.STRUCT (structure,loc) ->
       KtopDecl.NA loc
    | Fglobal.STATEMENT fblk ->
       begin
         try
           let blkL = of_block strV fblk in
           let stmt = Kstmt.Block (blkL,Klocs.dummy) in
           KtopDecl.S (stmt,Klocs.dummy)
         with
           e ->
           X.pn_s "EXCEPK" ("\nException occured at Statement:");
           X.pf_s "EXCEPK" VcpTranslate.Global.pprint g;
           print_endline ("Exception occured at Global:STATEMENT");
           KtopDecl.NA Klocs.dummy
           (*  raise e *)
       end
    | Fglobal.PROC (proc,fml1,fml2,fmlfmlL,loc) ->
       (* IGNORED: fml1 (precond?), fml2 (postcond?), fmlfmlL (??) *)
       begin
         let (fexp,fblkL,fblk) = proc in
         let fname = Fexp.toStr fexp in
         try
           let tpLvalL = List.map from_fblk_to_decl fblkL in
           let declPrmL = List.map (fun (tp,lval) -> Kdecl.Decl(tp,lval,Kinit.None)) tpLvalL in
           let stmtBody = Kstmt.Block (of_block strV fblk,loc) in
           let tp = get_rettype_of_exp fexp in
           KtopDecl.F (tp,fname,declPrmL,stmtBody,loc)
         with e ->
           X.pn_s "EXCEPK" ("\nException occured at Procedure: " ^ fname);
           X.pf_s "EXCEPK" VcpTranslate.Global.pprint g;
           print_endline ("Exception occured at Global.PROC: " ^ (Klocs.to_string loc));
           KtopDecl.NA Klocs.dummy
           (* raise e *)
       end
    | Fglobal.FFILE (st, _) ->
       let fin = open_in st in
       let g : Fglobal.t = Marshal.from_channel fin in
       close_in fin;
       of_global strV g
      
  let of_program strV (fprog : Fprogram.t) : Kprogram.t =
    List.map (of_global strV) fprog
    
  let of_module (fmodule : Fmodule.t) : Kmodule.t =
    (**
       module V = Map.Make(Bytes)
       aliases: bytes V.t
       eg.
        typedef struct X Y;    //aliases is  [Y -> X]
        typedef Y Z;           //aliases is  [Y -> X; Z -> Y]

        therefore,
        1. if 'x' is 'V.find y aliases' then it means 'typedef x y;' exists in the sourcecode.
        2. if 'x' is 'V.find x aliases' then it means 'typedef struct x x' exists in the sourcecode.
        3. if 'x' is 'V.find y aliases' and 'z' is 'V.find x aliases' but 'V.find z aliases' gives Not_found exception, then 'z' is the original structure and both x and y are its aliases.
     *)
    let (filename,filepath,fprog,fstructureL',_,_,aliases) = fmodule in
    print_mes filename "Converting from F to K...";
    (* conversion of structures *)    
    let fstructureL = List.map snd (V.bindings fstructureL') in
    let structureV : Kstructure.t V.t =
      List.fold_left
        (fun v s ->
          let kstructure = of_structure s in
          let name = fst kstructure in
          V.add name kstructure v)
        V.empty
        fstructureL
    in
    (* conversion of prog *)
    let prog = of_program structureV fprog in
    let prog1 = prog in
    (* creating kmodule *)
      let kmodule = (filename,filepath,structureV,aliases,prog1) in
    (*
    print_endline "###################################";
    Fmodule.pprint fmodule;
    print_endline "###################################";
    Kmodule.println kmodule;
    print_endline "###################################";
     *)
    kmodule

    
end
;;


module ConvKtoF = struct

  let rec of_attr attr =
    match attr with
    | T.PTR -> Fexp.PTR
    | T.HAT -> Fexp.HAT
    | T.BAR -> Fexp.BAR
    | T.DOT -> Fexp.DOT
    | T.TILDE -> Fexp.TILDE
    | T.CHECK -> Fexp.CHECK
    | T.DOTDOT -> Fexp.DOTDOT
    | T.ACUTE -> Fexp.ACUTE
    | T.QUESTION -> Fexp.QUESTION
    | T.EXQ -> Fexp.EXQ
    | T.ARRAY nn -> Fexp.ARRAY (List.map (fun n -> Fexp.CONST n) nn)
    | T.PARAM -> Fexp.PARAM
    | T.PTRPTR -> Fexp.PTRPTR
    | T.SIMPLE n -> Fexp.SIMPLE n
    | T.GLOBAL -> Fexp.GLOBAL
    | T.EXTERN -> Fexp.EXTERN
    | T.PROTO -> Fexp.FUNCPTR ([],[])
    | T.FUNC -> Fexp.FUNC ([],[])
    | T.INDIRECT -> Fexp.INDIRECT
    | T.NESTED -> Fexp.NESTED                  
    | T.STRUCT name -> Fexp.STRUCT name

  (* Kimura's SHterm -> Faisal's Exp *)
  let rec of_term_e t =
	match t with
	| T.Var (v,attrs) -> Fexp.VAR(v, List.map of_attr attrs)
	| T.Int n -> Fexp.CONST n
	| T.Add tt ->
	  let e1 = try List.nth (List.map of_term_e tt) 0  with _ -> raise (X.StError "Nth: convFtoK-1") in
	  let e2 = try List.nth (List.map of_term_e tt) 1  with _ -> raise (X.StError "Nth: convFtoK-1") in
	  Fexp.BINOP (e1,Fop.ADD,e2)
	| T.Sub tt ->
	  let e1 = try List.nth (List.map of_term_e tt) 0 with _ -> raise (X.StError "Nth: convFtoK-1") in
	  let e2 = try List.nth (List.map of_term_e tt) 1 with _ -> raise (X.StError "Nth: convFtoK-1") in
	  Fexp.BINOP (e1,Fop.SUB,e2)
	| T.Mul (t1,t2) ->
	   let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.MUL,e2)
	| T.Mod (t1,t2) ->
	   let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.MOD,e2)
    | T.Div (t1,t2) -> 
       let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.DIV,e2)
    | T.Shr (t1,t2) ->
       let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.SHR,e2)
    | T.Shl (t1,t2) ->
       let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.SHL,e2)
    | T.Band (t1,t2) ->
       let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.BAND,e2)
    | T.Bor (t1,t2) ->
       let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.BOR,e2)
    | T.Bxor (t1,t2) -> (* not supported in vcpBase *)
       let e1 = of_term_e t1 in
       let e2 = of_term_e t2 in
	   Fexp.BINOP (e1,Fop.XOR,e2)
    | T.Bnot t1 -> (* not supported in vcpBase *)
	   Fexp.NOTHING
    | T.Offset (strName,t0) ->
       let e0 = of_term_e t0 in
       Fexp.OFFSET (strName,e0)
    | T.Fcall (g,tt) ->
       match g,tt with
       | "#ARROW", t1::T.Var (field,_)::_ ->
          let fexp1 = of_term_e t1 in
          Fexp.ARROW (fexp1,field)
       | "#ADDR", t1::_ ->
          let fexp1 = of_term_e t1 in
          Fexp.ADDR fexp1
       | "#LBL", T.Var (label,_)::t1::_ ->
          let fexp1 = of_term_e t1 in
          Fexp.LBL (label,fexp1)
       | _,_ -> Fexp.NOTHING (* it is supported in of_term_t *)

  (* Kimura's SHterm -> Faisal's Term *)
  let rec of_term_t t = 
	match t with
	| T.Fcall (g,tt) ->
     let uu = List.map of_term_e tt in
     Ftm.EXP (Fexp.FCALL (g,uu))
  | _ -> Ftm.EXP (of_term_e t)

  let rec of_pure p =
    match p with
    | P.Atom (op,tt) ->
	   let t0 = try List.nth tt 0 with _ -> raise (X.StError "Nth: convFtoK-1") in
	   let t1 = try List.nth tt 1 with _ -> raise (X.StError "Nth: convFtoK-1") in
       let tm0 = of_term_t t0 in
       let tm1 = of_term_t t1 in
       begin
	     match op with
	     | P.Eq -> tm0 =..= tm1
	     | P.Neq -> tm0 <..> tm1
	     | P.Le -> tm0 <..= tm1
	     | P.Lt -> tm0 <..< tm1
         | P.In ->
            (* (In,[t0;t1;t2]) is "t0 in (t1,t2)" i.e. t1<=t0 and t0<=t2 *)
            let t2 = try List.nth tt 2 with _ -> raise (X.StError "Nth: convFtoK-1") in
            let tm2 = of_term_t t2 in
            (tm1 <..= tm0) &..& (tm0 <..= tm2)
         | P.Out ->
            (* (Out,[t0;t1;t2]) is "t0 notin (t1,t2)" i.e. (t0<t1 or t2<t0) and t1<=t2 *)
            let t2 = try List.nth tt 2 with _ -> raise (X.StError "Nth: convFtoK-1") in
            let tm2 = of_term_t t2 in
            (tm1 <..= tm2) &..& ((tm0 <..< tm1) |..| (tm2 <..< tm0)) 
         | P.Disj ->
            (* (Disj,[t0;t1;t2;t3]) is "(t0,t1) disj (t2,t3)" i.e. t0<=t1 and t2<=t3 and (t1<t2 or t3<t0) *)
            let t2 = try List.nth tt 2 with _ -> raise (X.StError "Nth: convFtoK-1") in
            let tm2 = of_term_t t2 in
            let t3 = try List.nth tt 3 with _ -> raise (X.StError "Nth: convFtoK-1") in
            let tm3 = of_term_t t3 in
            (tm0 <..= tm1) &..& ((tm2 <..= tm3) &..& ((tm1 <..< tm2) |..| (tm3 <..< tm0)))
         | P.Comm ->
            (* (Comm,[t0;t1;t2;t3]) is "(t0,t1) comm (t2,t3)" i.e. t0<=t1 and t2<=t3 and t2<=t1 and t0<=t3 *)
            let t2 = try List.nth tt 2 with _ -> raise (X.StError "Nth: convFtoK-1") in
            let t3 = try List.nth tt 3 with _ -> raise (X.StError "Nth: convFtoK-1") in            
            let tm2 = of_term_t t2 in
            let tm3 = of_term_t t3 in
            (tm0 <..= tm1) &..& ((tm2 <..=tm3) &..& ((tm2 <..= tm1)  &..& (tm0 <..= tm3)))
       end
    | P.And pp ->
       let _True = (Ftm.NULL =..= Ftm.NULL) in
       List.fold_right (fun p -> fun q -> if q = _True then of_pure p else ((of_pure p) &..& q) ) pp _True
    | P.Or pp ->
       let _False = (Ftm.NULL <..> Ftm.NULL) in
       List.fold_right (fun p -> fun q -> if q = _False then of_pure p else ((of_pure p) |..| q)) pp _False
    | P.True ->
       fzero =..= fzero
    | _ ->
       Fbex.NOTHING (* unsupport *)
         
  let of_pure_And p =
    match p with
    | P.And pp -> List.map of_pure pp
    | _ -> [of_pure p]

  let of_spatexp_pointer s : F.Pointer.t list =
	match s with
	| S.Pto(t,cc) ->
	  let t' = of_term_t t in
	  let cc' = List.map (fun (f,t) -> (f, of_term_t t)) cc in
	  [(t',cc')]
	| _ -> []

  let of_spatexp_predicate s : F.Predicate.t list =
	match s with
	| S.Arr(t1,t2) ->
	  let t1' = of_term_t t1 in
	  let t2' = of_term_t t2 in
	  [("Array", [t1';t2'])]
    | S.Str(t1,t2) ->
	  let t1' = of_term_t t1 in
	  let t2' = of_term_t t2 in
	  [("Stringpart", [t1';t2'])]
	| _ -> []	

  let of_sh (sh : SH.t) = 
	let (_,p,ss) = sh in
	let pp' = of_pure_And p in
	let ptr' = List.concat (List.map of_spatexp_pointer ss) in
	let pred' = List.concat (List.map of_spatexp_predicate ss) in
	([], pp', ptr', pred')

  let of_qfsh (sh : QFSH.t) = 
	let (p,ss) = sh in
	let pp' = of_pure_And p in
	let ptr' = List.concat (List.map of_spatexp_pointer ss) in
	let pred' = List.concat (List.map of_spatexp_predicate ss) in
	([], pp', ptr', pred')
    
  let of_interval (invl : Invl.t) =
    let (t1,t2) = invl in
    let tm1 = of_term_t t1 in
    let tm2 = of_term_t t2 in
    (tm1,tm2)
                                               
  let of_segment (seg : Seg.t) =
    List.map (fun invl -> of_interval invl) seg

  (* from Kimura's parsed manual-input data to Faisal's data 
    It returns (function_prototype,s,d,A,[(r,s',d',A',B')]) in Faisal's data structure
    where function_prototype has the form ([PTO],"func-name",[("x",[PTO;STRUCT "list"])]) that means
    int* func-name (struct list* x);
   *)
  let of_MIfile (file : MIfile.t) =
    let of_mytype tp = List.map of_attr tp in
    let of_param params = List.map (fun (v,tp)->(v,of_mytype tp)) params in
    let of_store s = List.map (fun (v,t)->(v,of_term_t t)) s in
    let of_return (r,s,d,shA,shB) = (of_term_t r, of_store s, of_pure d, of_qfsh shA, of_qfsh shB) in
    let of_functionIO funIO = 
      let f_fproto = List.map
                       (fun (ret_tp,funcname,param) -> (of_mytype ret_tp,funcname,of_param param))
                       funIO.MIfunctionIO.func
      in
      let f_s = of_store funIO.MIfunctionIO.s in (* store s *)
      let f_d = of_pure funIO.MIfunctionIO.d in (* branch-condition d *)
      let f_A = of_qfsh funIO.MIfunctionIO.sh in (* precondition A *)
      let f_ret = List.map of_return funIO.MIfunctionIO.ret in (* returns *)
      (f_fproto,f_s,f_d,f_A,f_ret)
    in
    List.map of_functionIO file

end
;;

let decide_ps_faisal f_entL =
  (* Default Options of entailment checker              *)
  (* opt=true    : optimizing with unsat-checking is ON *)
  (* frame=true  : frame-elimination is ON              *)
  (* debug=false : debugging mode is OFF                *)
  (* If you want to change these options, use the following functions *)
  (* unset_opt ();      *)
  (* unset_frame();     *)
  (* set_debug();       *)
  let ps = ConvFtoK.of_entlL f_entL in
  let psnf = PS.nf ps in
  EntlcheckA.decide_ps psnf
;;


(* Brotherston's entailment checker *)
let decide_ps_faisal_b f_entL =
  let ps = ConvFtoK.of_entlL f_entL in
  let psnf : Entl.t list = PS.nf ps in
  (* let left : QFSH.t list = List.map (fun ((_,ppp,ss),_) -> (ppp,ss)) psnf in
  let right : QFSH.t list = List.concat (List.map (fun (_,r) -> List.map (fun (_,ppp,ss) -> (ppp,ss)) r) psnf) in
  Entlcheck_b.entlcheck (List.hd left, right) *)
  (* PS.println psnf; *)
  let r = EntlcheckA.decide_ps psnf in
  r
;;

(* Brotherston's satchecker *)
exception UnsatCore of QFSH.t * Z3.Expr.expr list
;;

(* flags for satchecker *)
let decide_ps_faisal_sat_pb f_entL =
    let ps = ConvFtoK.of_entlL f_entL in
    let psnf = PS.nf ps in
    let shL = List.map (fun ((_,p,ss),_) -> (p,ss)) psnf in
  let _res = ref true in
  let _ucflag = ref false in
  begin
    try
      for i = 0 to List.length shL - 1 do
        let sh = List.nth shL i in
        X.pf_s "UNSATCORE" (fun _ -> _ucflag := true) ();
        let modelflag = false in
        let bnflag = true in
        (* Ftools.pi i; *)
        match Satcheck.satcheck_bn modelflag !_ucflag bnflag sh with
        | SatResult.Model _ -> (* Ftools.pn "@@SATCHECK"; *) ()
        | SatResult.UnsatCore uc -> raise (UnsatCore (sh,uc)) (* uc is an unsatcore symbolic heap *)
        | SatResult.Unknown -> raise (UnsatCore (sh,[])) (* dummy *)
      done;
    with
      UnsatCore (sh,uc) ->
      _res.contents <- false;
      X.pf_s "UNSAT" print_endline @@ (QFSH.to_string sh) ^ " is unsat";
      X.pf_s "UNSAT" print_endline @@ "[Unsat core]";
      X.pf_s "UNSAT" (List.iter (fun e -> print_endline (Z3.Expr.to_string e))) uc
  end;
  !_res
;;

let biabduction f_fml1 f_fml2 =
  let module BA = Biabd.BAanswer in
  let (_,p1,ss1) = try ConvFtoK.of_oneformula f_fml1 with _ -> raise (X.StError "Nth: biabd-21") in
  let (_,_,ss2) = try ConvFtoK.of_oneformula f_fml2 with _ -> raise (X.StError "Nth: biabd-22") in
  let answer = ref [] in

  let baL = Biabd.biabduction [] p1 ss1 ss2 in (* baL: biabduction answer list *)
  for i = 0 to List.length baL - 1 do
    let ba = List.nth baL i in
    let sh1 = (P.And ba.BA.pp, ba.BA.ssX) in
    let sh2 = (P.True, ba.BA.ssY) in
    let fml1 = ConvKtoF.of_qfsh sh1 in
    let fml2 = ConvKtoF.of_qfsh sh2 in
    (*
	answer := try [ (fml1,fml2) ] with _ ->  raise (X.StError "Nth: biabd-23")
     *)
    answer := (fml1,fml2) :: !answer;
  done;
  
  !answer
;;

let biabduction2 f_fml1 f_fml2 =
  (* VcpBase.Formula.print f_fml1; *)
  let module BA = Biabd.BAanswer in
  let (_,p1,ss1) = try ConvFtoK.of_oneformula f_fml1 with _ -> raise (X.StError "Nth: biabd-21") in
  let (_,_,ss2) = try ConvFtoK.of_oneformula f_fml2 with _ -> raise (X.StError "Nth: biabd-22") in
  let answer = ref [] in
  (*>>>>>*)
  Ftools.pf_s "BIABD" print_newline ();
  Ftools.pf_s "BIABD" print_newline ();  
  Ftools.pf_s "BIABD" print_endline 
    ("- BIABDUCTION QUERY\n" ^
    "A: " ^ (P.to_string p1) ^ " & " ^ (SS.to_string ss1) ^ "\n" ^
    "B: " ^ (SS.to_string ss2));
  (*<<<<<<*)
  let (baL,pp) = Biabd.biabduction2 [] p1 ss1 ss2 in
  for i = 0 to List.length baL - 1 do
    let ba = List.nth baL i in
    let sh1 = (P.And (p1::ba.BA.pp), ba.BA.ssX) in (* added the original pure-part to biabduction answers *)
    let sh2 = (P.True, ba.BA.ssY) in
    let fml1 = ConvKtoF.of_qfsh sh1 in
    let fml2 = ConvKtoF.of_qfsh sh2 in
    answer := (fml1,fml2) :: !answer;
    (*>>>>>>*)
    Ftools.pf_s "BIABD" print_endline "";
    Ftools.pf_s "BIABD" print_endline ("-- BEGIN (BIABDUCTION ANSWER: " ^ (string_of_int i) ^ ")");
    Ftools.pf_s "BIABD" print_endline ">>> kimura";
    Ftools.pf_s "BIABD" BA.println ba;
    Ftools.pf_s "BIABD" print_endline "";    
    Ftools.pf_s "BIABD" print_endline ">>> faisal";
    (* VcpBase.Formula.print fml1; *)
    Ftools.pf_s "BIABD" flush_all ();
    Ftools.pf_s "BIABD" print_newline ();
    (* VcpBase.Formula.print fml2; *)
    Ftools.pf_s "BIABD" flush_all ();
    Ftools.pf_s "BIABD" print_newline ();    
    Ftools.pf_s "BIABD" print_endline ("-- END (BIABDUCTION ANSWER: " ^ (string_of_int i) ^ ")");
    (*<<<<<<*)
  done;
  let f_unsatL = List.map ConvKtoF.of_pure pp in
  (!answer,f_unsatL)
;;


(*----------------*)
(* Union interval *)
(*----------------*)
(* f_seg is _Sk_i_m in vcpPrecond2 *)
let union f_cond f_seg = 
  let answer = ref [] in
  let k_seg = ConvFtoK.of_segment f_seg in
  let cond = ConvFtoK.of_bexpL f_cond in
  let unint = unionInterval2 cond k_seg in (* list of (seg,cond) *)
  for i = 0 to List.length unint - 1 do
    let (k_seg1,k_cond1) = List.nth unint i in
    let f_seg1 = ConvKtoF.of_segment k_seg1 in
    let f_cond1 = ConvKtoF.of_pure k_cond1 in
    answer := (f_seg1,f_cond1) :: !answer
  done;
  !answer
;;

(*--------------*)  
(* Max interval *)
(*--------------*)  
(* f_seg is _Sk_i_m in vcpPrecond2 *)
let max_interval f_cond f_seg = 
  let answer = ref [] in
  let k_seg = ConvFtoK.of_segment f_seg in
  let cond = ConvFtoK.of_bexpL f_cond in
  let maxinvl = Interval.maxInterval cond k_seg in (* list of (invl,cond) *)
  for i = 0 to List.length maxinvl - 1 do
        let (k_invl,k_cond) = List.nth maxinvl i in
    let f_invl = ConvKtoF.of_interval k_invl in
    let f_cond = ConvKtoF.of_pure k_cond in
    answer := (f_invl,f_cond) :: !answer
  done;
  !answer
;;

(*--------------*)  
(* Manual input *)
(*--------------*)  
(****************
This returns Faisal's data of parsed input
The output data structure is [(f_fproto,f_s,f_d,f_A,f_ret)], where
 f_fproto:: function prototype. 
     ([PTO], "func-name", [("x",[PTO;STRUCT "list"])]) : attr list * string * (string, attr list) list
     This means int* func-name (struct list* x);
 f_s:: store. [("v",term)]: (string * Term.t) list
 f_d:: branch. <pure-formula>: BExp.t
 f_A:: precondition. <symbolic-heap>: Formula_0 (where (Formula_0 list) means Formula.t)
 f_ret:: return info. (r,s,d,A,B): Term.t * [store's type] * [branch's type] * Formula_0 * Formula_0
****************)
let manual_input filename =
  let input_str = my_read_file filename in
  let miFile =  Manualinput.parse input_str in
  ConvKtoF.of_MIfile miFile 
;;
  
(*---------------------------*)  
(* function pointer analysis *)
(*---------------------------*)

let fp_preAnalyze_a_module (fmodule: VcpAllC.t) mod_id : MyFp.kdata * Kprogram.t =
  let kmodule = ConvFCtoKC.of_module fmodule in
  let (mod_name,_,_,_,fundefL) = kmodule in
  print_mes "PRE" ("Pre-Analysis of " ^ mod_name ^ " begins");
  Ftools.pf_s "FPAdebug" print_endline "-----------------------";
  Ftools.pf_s "FPAdebug" Fmodule.pprint fmodule;
  Ftools.pf_s "FPAdebug" print_endline "-----------------------";
  Ftools.pf_s "FPAdebug" Kmodule.println kmodule;
  Ftools.pf_s "FPAdebug" print_endline "-----------------------";
  
  (* PreAnalysis *)
  let kdata = MyFp.preAnalyze_a_module kmodule mod_id in
  print_mes "PRE" ("Pre-Analysis of " ^ mod_name ^ " ends");
  (kdata,fundefL)
;;

let fp_top_level slacDataDir fname sp_tm =

  let gt3 = Sys.time () in  
  let (r,funpos) = MyFp.mainAnalysis slacDataDir fname sp_tm in
  let gt4 = Sys.time () in
  (* output = [(fname1,fp1,pos1,fnameL1);(fname2,fp2,pos2,fnameL2)] *)
  let output : ((bytes * bytes * int) * bytes list) list = FpPos.toOutput funpos in
  
  match r with
  | MyFp.FPstate.None ->
     X.dbg "GC" "After Conversion:" X.print_gc (Gc.stat ());
     let sh_dummy = FPsh.dummy in
     (sh_dummy,output)
  | MyFp.FPstate.SH sh ->
     let (s,h) = sh in
     X.dbg "GC" "After FPA main:" X.print_gc (Gc.stat ());
     Ftools.pf_s "FPAresult" print_endline "";
     Ftools.pf_s "FPAresult" print_endline ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
     print_endline @@ "Missing functions";
     print_endline @@ (string_of_list (fun x->x) " " MyFp.az.MyFp.Analyzer.missingFunlist);
     Ftools.pf_s "FPAresult" print_endline ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>";     
     Ftools.pf_s "FPAresult" print_string' "[s_fp]\n";
     Ftools.pf_s "FPAresult" FPsh.println_s_fp s;
     Ftools.pf_s "FPAresult" print_string' "\n[s_fppos]\n";
     Ftools.pf_s "FPAresult" FpPos.println funpos;
     Ftools.pf_s "FPAresult" print_endline ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
     print_endline @@ "Missing FP: " ^ (string_of_int MyFp.gi.MyFp.GlobalInfo.missingFP);
     print_endline ("Main FPA time:" ^ (string_of_float (gt4-.gt3)));
     Ftools.pf_s "FPAresult" print_endline ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>";
     (sh,output)
;;
