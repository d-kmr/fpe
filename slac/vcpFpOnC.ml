open Ftools;;
open Yojson.Basic.Util;;
module C = Cabs;;
module V = Map.Make(Bytes);;
         
type ifpvar = {name : string; in_fun : string; to_funs : string list;} [@@deriving of_yojson];;
type ifpfld = {ptr: string; fld : (int * string * string) list; in_fun : string; to_funs : string list;} [@@deriving of_yojson];;
type ifparr = {ptr: string; in_fun : string; to_funs : string list;} [@@deriving of_yojson];;
type ifptyp = FPVAR of ifpvar | FPFLD of ifpfld | FPARR of ifparr [@@deriving of_yojson];;
type ifproot = ifptyp list [@@deriving of_yojson];;

exception SVFJSONParseError of string
exception HeuristicFails
                             
let sanitize str =
  try
    let i = Bytes.index str '.' in
    Bytes.sub str 0 i
  with
    Not_found ->
    str
;;

let sanitize_tp str =
  try
    let i = Bytes.index str '.' in
    Bytes.sub str (i+1) (Bytes.length str - i - 1)
  with
    Not_found ->
    str
;;
                             
let pp_ifptyp = function
    FPVAR ifpvar ->
     pw "VAR"; pw (sanitize ifpvar.name); p "-->"; iterS p "," ifpvar.to_funs
  | FPFLD ifpfld ->
     pw "FLD"; pw (sanitize ifpfld.ptr); iterS (fun (i,s,tp) -> pl i; pw ""; pw s; p tp) "," ifpfld.fld; p "-->"; iterS p "," ifpfld.to_funs
  | FPARR ifparr ->
     pw "ARR"; pw (sanitize ifparr.ptr); p "-->"; iterS p "," ifparr.to_funs
;;
                             
let value k assoc =
  assoc |> member k |> to_string
;;

let int_value k assoc =
  assoc |> member k |> to_int
;;

let parse_list json =
  [json] |> flatten |> List.map to_string
;;

let parse_field json =
  let nm = value "fld_name" json in
  let idx = int_value "fld_index" json in
  let tp = value "tp" json in
  (idx, tp, nm)

let parse_list_of_field json =
  let field_data = [json] |> flatten in
  field_data |> List.map parse_field
;;

let parse_var data =
  let assoc = data |> (fun ls -> List.nth ls 1) in
  let name = assoc |> value "name" in
  let in_fun = assoc |> value "in_fun" in
  let to_funs = assoc |> member "to_funs" |> parse_list in
  {name=name; in_fun=in_fun; to_funs=to_funs}
;;

let parse_fld json =
  let assoc = json |> (fun ls -> List.nth ls 1) in
  let ptr = assoc |> value "ptr" in
  let fld = assoc |> member "fld" |> parse_list_of_field in
  let in_fun = assoc |> value "in_fun" in
  let to_funs = assoc |> member "to_funs" |> parse_list in
  {ptr=ptr; fld=fld; in_fun=in_fun; to_funs=to_funs}
;;

let parse_arr json =
  let assoc = json |> (fun ls -> List.nth ls 1) in
  let ptr = assoc |> value "ptr" in
  let in_fun = assoc |> value "in_fun" in
  let to_funs = assoc |> member "to_funs" |> parse_list in
  {ptr=ptr; in_fun=in_fun; to_funs=to_funs}
;;

let parse_typ json (* : Yojson.Basic.t -> ifptyp *) =
  let data = [json] |> flatten in
  let typ = data |> (fun ls -> List.nth ls 0) |> to_string in
  if typ = "FPFLD" then
    let v = parse_fld data in
    FPFLD v
  else if typ = "FPVAR" then
    let v = parse_var data in
    FPVAR v
  else if typ = "FPARR" then
    let v = parse_arr data in
    FPARR v
  else
    raise (SVFJSONParseError typ)
;;

let parse_root json (* : Yojson.Basic.t -> ifproot *) =
  [json] |> flatten |> List.map parse_typ
;;
  

let get_fpdata () =
  if !VcpBase.Options.fp_json_file = "" then
    []
  else
    begin
      let json = Yojson.Basic.from_channel (open_in !VcpBase.Options.fp_json_file) in
      let fpdata = parse_root json in
      fpdata
    end
;;

let get_fpvar fpdata var =
  try
    Some (
        List.find (function FPVAR v -> sanitize v.name = var | _ -> false) fpdata)
  with
    Not_found ->
    None
;;

let get_fparr fpdata var =
  try
    Some (
        List.find (function FPARR v -> sanitize v.ptr = var | _ -> false) fpdata)
  with
    Not_found ->
    None
;;

let rec get_ptr_fields = function
  | C.MEMBEROF (C.VARIABLE ptr, fld) ->
     (Some ptr, [fld])
  | C.MEMBEROFPTR (C.VARIABLE ptr, fld) ->
     (Some ptr, [fld])
  | C.MEMBEROF (C.INDEX (expression,_), fld) ->
     get_ptr_fields (C.MEMBEROF (expression, fld))
     
  | C.MEMBEROFPTR (C.INDEX (expression,_), fld) ->
     get_ptr_fields (C.MEMBEROF (expression, fld)) 
  | C.MEMBEROF (expression, fld) ->
     let (ptr, flds) = get_ptr_fields expression in
     (ptr, flds @ [fld])
  | C.MEMBEROFPTR (expression, fld) ->
     let (ptr, flds) = get_ptr_fields expression in
     (ptr, flds @ [fld])
  | C.PAREN (expression) ->
     get_ptr_fields expression
  | e ->
    
     (None, [])
;;

let get_field_by_index (structures:(bytes * (VcpBase.Exp.t * VcpBase.Term.t) list * VcpBase.Exp.t list option) V.t) (i, tp, nm) =
  let is_prefix a b =
    let l = Bytes.length a in
    if l <= Bytes.length b then
      if a = Bytes.sub b 0 l then
        true
      else
        false
    else
      false
  in
  let (_, flds, _) =
    try
      V.find (sanitize_tp tp) structures
    with
      Not_found ->

      let st  = V.filter (fun k (_, v, _) ->
                    List.length v > i && is_prefix (VcpBase.Exp.toStr (fst (List.nth v i))) nm ) structures in
      let lst = V.bindings st in
      
      if V.cardinal st = 1 then
        snd (List.hd lst)
      else
        let (_, h, _) = snd (List.hd lst) in
        let h' : VcpBase.Exp.t list = fst |>>| h in 
        if List.for_all (fun (_, y, _) -> fst |>>| y = h') (snd |>>| (List.tl lst)) then
          snd (List.hd (V.bindings st))
        else
          raise HeuristicFails
  in

  let (fld, _) = List.nth flds i in
  let r = VcpBase.Exp.toStr fld in
  r
;;
;;

let pp_st structures =
  V.iter (fun k (_,flds,_) ->
      pw k;
      iterS (fun (x,_) -> p (VcpBase.Exp.toStr x)) "," flds; pn ""
    ) structures

;;



let get_fld_fp structures fpdata expression =
  
  let (ptr, flds) = get_ptr_fields expression in
  match ptr with
    Some ptr ->
     begin
       try
         let r =
           (List.find (function FPFLD v ->
                                 let vptr = sanitize v.ptr in
                                 vptr = ptr && (get_field_by_index structures) |>>| v.fld = flds | _ -> false) fpdata)
         in
         Some r
       with
         Not_found -> None
     end
  | None -> None
;;


let rec fpcalls_in_expression structures fpdata expression =

  match expression with
    C.NOTHING -> []
  | C.UNARY (_, expression) ->
     fpcalls_in_expression structures fpdata expression
  | C.LABELADDR _ -> []
  | C.BINARY (_, expression1, expression2) ->
     fpcalls_in_expression structures fpdata expression1 @@
       fpcalls_in_expression structures fpdata expression2
  | C.QUESTION (expression1, expression2, expression3) ->
     fpcalls_in_expression structures fpdata expression1 @@
       fpcalls_in_expression structures fpdata expression2 @@
         fpcalls_in_expression structures fpdata expression3
  | C.CAST (_, init_expression) ->
     begin
       let rec aux = function
           C.NO_INIT -> []
         | C.SINGLE_INIT expression ->
            fpcalls_in_expression structures fpdata expression
         | C.COMPOUND_INIT ls ->
            List.concat (aux |>>| (snd |>>| ls))
       in
       aux init_expression
     end  
  | C.CALL (C.VARIABLE fname, expression_list) ->
     begin
       match get_fpvar fpdata fname with
         Some d ->
          (C.VARIABLE fname, d)::List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
       | None ->
          List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
     end
  | C.CALL (C.UNARY(C.MEMOF, C.VARIABLE fname), expression_list) ->
     begin
       match get_fpvar fpdata fname with
         Some d ->
          (C.VARIABLE fname, d)::List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
       | None ->
          List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
     end
  | C.CALL (C.PAREN(C.UNARY(C.MEMOF, C.VARIABLE fname)), expression_list) ->
     begin
       match get_fpvar fpdata fname with
         Some d ->
          (C.VARIABLE fname, d)::List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
       | None ->
          List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
     end
  | C.CALL (expression, expression_list) ->
     begin
       let fpfld = get_fld_fp structures fpdata expression in
       match fpfld with
         Some d ->
          (expression, d)::List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
       | None -> 
          fpcalls_in_expression structures fpdata expression @@
            List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
     end
  | C.COMMA expression_list ->
     List.concat ((fpcalls_in_expression structures fpdata) |>>| expression_list)
  | C.CONSTANT constant -> []
  | C.PAREN expression -> fpcalls_in_expression structures fpdata expression
  | C.VARIABLE string -> []
  | C.EXPR_SIZEOF expression -> fpcalls_in_expression structures fpdata expression
  | C.TYPE_SIZEOF _ -> []
  | C.EXPR_ALIGNOF expression -> fpcalls_in_expression structures fpdata expression
  | C.TYPE_ALIGNOF _ -> []
  | C.INDEX (expression1, expression2) ->
     fpcalls_in_expression structures fpdata expression1 @@
       fpcalls_in_expression structures fpdata expression2
  | C.MEMBEROF (expression, _) -> fpcalls_in_expression structures fpdata expression
  | C.MEMBEROFPTR (expression, _) ->  fpcalls_in_expression structures fpdata expression
  | C.GNU_BODY block -> fpcalls_in_block structures fpdata block
  | C.EXPR_PATTERN _ -> []

and fpcalls_in_block structures fpdata block =
  List.concat ((fpcalls_in_statement structures fpdata) |>>| block.C.bstmts)
  
and fpcalls_in_statement structures fpdata statement =
  match statement with
  | C.NOP _ -> []
  | C.COMPUTATION (expression, _) -> fpcalls_in_expression structures fpdata expression
  | C.BLOCK (block, _) -> fpcalls_in_block structures fpdata block
  | C.SEQUENCE (statement1, statement2, _) ->
     fpcalls_in_statement structures fpdata statement1 @@
       fpcalls_in_statement structures fpdata statement2
  | C.IF (expression, statement1, statement2, _) ->
     fpcalls_in_expression structures fpdata expression @@
       fpcalls_in_statement structures fpdata statement1 @@
         fpcalls_in_statement structures fpdata statement2
  | C.WHILE (_, expression, statement, _) ->
     fpcalls_in_expression structures fpdata expression @@
       fpcalls_in_statement structures fpdata statement
  | C.DOWHILE (_, expression, statement, _) ->
     fpcalls_in_expression structures fpdata expression @@
       fpcalls_in_statement structures fpdata statement
  | C.FOR (_, for_clause, expression1, expression2, statement, _) ->
     fpcalls_in_expression structures fpdata expression1 @@
       fpcalls_in_expression structures fpdata expression2 @@
       fpcalls_in_statement structures fpdata statement
  | C.BREAK _ -> []
  | C.CONTINUE _ -> []
  | C.RETURN (expression, _) ->
     fpcalls_in_expression structures fpdata expression
  | C.SWITCH (expression, statement, _) ->
     fpcalls_in_expression structures fpdata expression @@
       fpcalls_in_statement structures fpdata statement
  | C.CASE (expression, statement, _) ->
     fpcalls_in_expression structures fpdata expression @@
       fpcalls_in_statement structures fpdata statement
  | C.CASERANGE (expression1, expression2, statement, _) ->
     fpcalls_in_expression structures fpdata expression1 @@
       fpcalls_in_expression structures fpdata expression2 @@
       fpcalls_in_statement structures fpdata statement
  | C.DEFAULT (statement, _) ->
     fpcalls_in_statement structures fpdata statement
  | C.LABEL (_, statement, _) ->
     fpcalls_in_statement structures fpdata statement
  | C.GOTO _ -> []
  | C.COMPGOTO (expression, _) -> fpcalls_in_expression structures fpdata expression
  | C.DEFINITION _ -> []
  | C.ASM _ -> []
  | C.TRY_EXCEPT (block1, expression, block2, _) ->
     fpcalls_in_block structures fpdata block1 @@
       fpcalls_in_expression structures fpdata expression @@
         fpcalls_in_block structures fpdata block2
  | C.TRY_FINALLY (block1, block2, _) ->
     fpcalls_in_block structures fpdata block1 @@
       fpcalls_in_block structures fpdata block2
;;


let rec substitute_expression (to_be, by) expression =
  if to_be = expression then
    by
  else
    match expression with
      C.NOTHING -> expression
    | C.UNARY (op, expression) ->
        C.UNARY (op, substitute_expression (to_be, by) expression)
    | C.LABELADDR _ -> expression
    | C.BINARY (op, expression1, expression2) ->
       C.BINARY (op,
                 substitute_expression (to_be, by) expression1,
                 substitute_expression (to_be, by) expression2)
    | C.QUESTION (expression1, expression2, expression3) ->
       C.QUESTION (substitute_expression (to_be, by) expression1,
                   substitute_expression (to_be, by) expression2,
                   substitute_expression (to_be, by) expression3)
    | C.CAST (tp, init_expression) ->
       C.CAST (tp, init_expression)
    | C.CALL (expression, expression_list) ->
       C.CALL (substitute_expression (to_be, by) expression,
               (substitute_expression (to_be, by)) |>>| expression_list)
    | C.COMMA expression_list ->
       C.COMMA ((substitute_expression (to_be, by)) |>>| expression_list)
    | C.CONSTANT constant ->
       expression
    | C.PAREN expression ->
       C.PAREN (substitute_expression (to_be, by) expression)
    | C.VARIABLE string ->
       expression
    | C.EXPR_SIZEOF expression ->
       C.EXPR_SIZEOF (substitute_expression (to_be, by) expression)
    | C.TYPE_SIZEOF _ ->
       expression
    | C.EXPR_ALIGNOF expression ->
       C.EXPR_ALIGNOF (substitute_expression (to_be, by) expression)
    | C.TYPE_ALIGNOF _ ->
       expression
    | C.INDEX (expression1, expression2) ->
       C.INDEX (substitute_expression (to_be, by) expression1,
                substitute_expression (to_be, by) expression2)
    | C.MEMBEROF (expression, fld) ->
       C.MEMBEROF (substitute_expression (to_be, by) expression, fld)
    | C.MEMBEROFPTR (expression, fld) ->
       C.MEMBEROFPTR (substitute_expression (to_be, by) expression, fld)
    | C.GNU_BODY block ->
       C.GNU_BODY (substitute_block (to_be, by) block)
    | C.EXPR_PATTERN _ ->
       expression

and substitute_init_expression (to_be, by) = function
    C.NO_INIT as ie -> ie
  | C.SINGLE_INIT expression ->
     C.SINGLE_INIT (substitute_expression (to_be, by) expression)
  | C.COMPOUND_INIT xs ->
     let f (iw, ie) =
       (iw, substitute_init_expression (to_be, by) ie)
     in
     C.COMPOUND_INIT (f |>>| xs)
    
and substitute_block (to_be, by) block =
  { C.blabels = block.C.blabels;
    battrs = block.C.battrs;
    bstmts = (substitute_statement (to_be, by)) |>>| block.C.bstmts
  }

and substitute_statement (to_be, by) statement =
  match statement with
  | C.NOP _ -> statement
  | C.COMPUTATION (expression, cl) ->
     C.COMPUTATION (substitute_expression (to_be, by) expression, cl)
  | C.BLOCK (block, cl) ->
     C.BLOCK (substitute_block (to_be, by) block, cl)
  | C.SEQUENCE (statement1, statement2, cl) ->
     C.SEQUENCE (substitute_statement (to_be, by) statement1,
                 substitute_statement (to_be, by) statement2,
                 cl)
  | C.IF (expression, statement1, statement2, cl) ->
     C.IF (substitute_expression (to_be, by) expression,
           substitute_statement (to_be, by) statement1,
           substitute_statement (to_be, by) statement2,
           cl)
  | C.WHILE (a, expression, statement, cl) ->
     C.WHILE (a,
              substitute_expression (to_be, by) expression,
              substitute_statement (to_be, by) statement,
              cl)
  | C.DOWHILE (a, expression, statement, cl) ->
     C.DOWHILE (a, substitute_expression (to_be, by) expression,
                substitute_statement (to_be, by) statement, cl)
  | C.FOR (a, for_clause, expression1, expression2, statement, cl) ->
     C.FOR (a,
            for_clause,
            substitute_expression (to_be, by) expression1,
            substitute_expression (to_be, by) expression2,
            substitute_statement (to_be, by) statement,
            cl)
  | C.BREAK _ -> statement
  | C.CONTINUE _ -> statement
  | C.RETURN (expression, cl) ->
     C.RETURN (substitute_expression (to_be, by) expression, cl)
  | C.SWITCH (expression, statement, cl) ->
     C.SWITCH (substitute_expression (to_be, by) expression,
               substitute_statement (to_be, by) statement, cl)
  | C.CASE (expression, statement, cl) ->
     C.CASE (substitute_expression (to_be, by) expression,
             substitute_statement (to_be, by) statement, cl)
  | C.CASERANGE (expression1, expression2, statement, cl) ->
     C.CASERANGE (substitute_expression (to_be, by) expression1,
                  substitute_expression (to_be, by) expression2,
                  substitute_statement (to_be, by) statement,
                  cl)
  | C.DEFAULT (statement, cl) ->
     C.DEFAULT (substitute_statement (to_be, by) statement, cl)
  | C.LABEL (a, statement, cl) ->
     C.LABEL (a, substitute_statement (to_be, by) statement, cl)
  | C.GOTO _ -> statement
  | C.COMPGOTO (expression, cl) ->
     C.COMPGOTO (substitute_expression (to_be, by) expression, cl)
  | C.DEFINITION _ -> statement
  | C.ASM _ -> statement
  | C.TRY_EXCEPT (block1, expression, block2, cl) ->
     C.TRY_EXCEPT (substitute_block (to_be, by) block1,
                   substitute_expression (to_be, by) expression,
                   substitute_block (to_be, by) block2,
                   cl)
  | C.TRY_FINALLY (block1, block2, cl) ->
     C.TRY_FINALLY (substitute_block (to_be, by) block1,
                    substitute_block (to_be, by) block2, cl)

and substitute_forclause (to_be, by) = function
    C.FC_EXP expression ->
     C.FC_EXP (substitute_expression (to_be, by) expression)
  | C.FC_DECL definition ->
     C.FC_DECL (substitute_definition (to_be, by) definition)

and substitute_definition (to_be, by) definition =  
  match definition with
    C.DECDEF (init_name_group, cabsloc) ->
    C.DECDEF (substitute_init_name_group (to_be, by) init_name_group, cabsloc)
  | _ ->
     definition

and substitute_init_name_group (to_be, by) (specifier, init_name_list) =
  (specifier, substitute_init_name (to_be, by) |>>| init_name_list)
  
and substitute_init_name (to_be, by) (name, init_expression) =
  (name, substitute_init_expression (to_be, by) init_expression)

;;


let make_var var = C.VARIABLE var
;;

let make_memberofptr structures ptr flds =
  let rec aux = function
      [] -> C.VARIABLE ptr
    | fld::flds -> C.MEMBEROFPTR (aux flds, fld)
  in
  aux (List.rev ((get_field_by_index structures) |>>| flds))
;;

let execute_transformation structures cabsloc fpdata statement (to_be, matched_fpdata) =
  match matched_fpdata with
    FPVAR v ->
     begin
       match v.to_funs with
         [] -> statement
       | hd_fun::tl_funs ->
          let else_statement = substitute_statement (to_be, make_var hd_fun) statement in
          (fun else_statement then_fun ->
            let cond = C.BINARY (C.EQ, C.VARIABLE v.name, C.VARIABLE then_fun) in
            let then_statement = substitute_statement (to_be, make_var then_fun) statement in
            C.IF (cond, then_statement, else_statement, cabsloc)
          ) |->> (else_statement, tl_funs)
     end
  | FPFLD v ->
     begin
       match v.to_funs with
         [] -> statement
       | hd_fun::tl_funs ->
          let else_statement = substitute_statement (to_be, make_var hd_fun) statement in
          (fun else_statement then_fun ->
            let cond = C.BINARY (C.EQ,
                                 make_memberofptr structures v.ptr v.fld,
                                 C.VARIABLE then_fun) in
            let then_statement = substitute_statement (to_be, make_var then_fun) statement in
            C.IF (cond, then_statement, else_statement, cabsloc)
          ) |->> (else_statement, tl_funs)
     end
  | FPARR v ->
     begin
       match v.to_funs with
         [] -> statement
       | hd_fun::tl_funs ->
          let else_statement = substitute_statement (to_be, make_var hd_fun) statement in
          (fun else_statement then_fun ->
            let cond = C.BINARY (C.EQ, C.VARIABLE v.ptr, C.VARIABLE then_fun) in
            let then_statement = substitute_statement (to_be, make_var then_fun) statement in
            C.IF (cond, then_statement, else_statement, cabsloc)
          ) |->> (else_statement, tl_funs)
     end
;;

  
(*
let rec is_a_fpcall fpdata = function
    C.VARIABLE fp -> List.exists (function FPVAR v -> v.name=fp | _ -> false) fpdata
  | C.MEMBEROF (exp, fld) | C.MEMBEROFPTR (exp, fld) ->
     List.exists (function FPFLD v ->
                            begin
                              match List.rev v.fld, exp with
                              | [], C.VARIABLE vname -> vname = v.ptr
                              | last::init, _ ->
                                 if last = fld then
                                   is_a_fpcall [] exp
                                 else
                                   false
                              | _, _ -> false
                            end
                         | _ -> false) fpdata
  | _ -> false
;; *)

let transform_expression_by_if structures cabsloc fpdata expression statement =
  let matched_fpdata = fpcalls_in_expression structures fpdata expression in
  if List.length matched_fpdata > 0 then 
    (execute_transformation structures cabsloc fpdata) |->> (statement, matched_fpdata) 
  else
    statement
;;

let rec build_conditional operand parameters = function
  | [] -> operand
  | [fn] ->
     let fnv = C.VARIABLE fn in
     C.CALL (fnv, parameters)
  | fn::fns ->
     let fnv = C.VARIABLE fn in
     C.QUESTION (
         C.BINARY (C.EQ, operand, fnv),
         C.CALL (fnv, parameters),
         build_conditional operand parameters fns
       )
;;

let make_conditional function_expression parameters = function
    [] -> function_expression
  | (exp, FPVAR v)::_ ->
     build_conditional function_expression parameters v.to_funs 
  | (exp, FPFLD v)::_ ->
     build_conditional function_expression parameters v.to_funs
  | (exp, FPARR v)::_ ->
     build_conditional function_expression parameters v.to_funs
;;

let rec get_arrptr = function
    C.VARIABLE v -> v
  | C.INDEX (exp, _) -> get_arrptr exp
  | C.PAREN (exp) -> get_arrptr exp
  | C.UNARY (C.MEMOF, exp) -> get_arrptr exp
  | _ -> raise (StError "Exception at Array Pointer")

let rec transform_expression structures fpdata expression =
    match expression with
      C.NOTHING -> expression
    | C.UNARY (op, expression) ->
        C.UNARY (op, transform_expression structures fpdata expression)
    | C.LABELADDR _ -> expression
    | C.BINARY (op, expression1, expression2) ->
       C.BINARY (op,
                 transform_expression structures fpdata expression1,
                 transform_expression structures fpdata expression2)
    | C.QUESTION (expression1, expression2, expression3) ->
       C.QUESTION (transform_expression structures fpdata expression1,
                   transform_expression structures fpdata expression2,
                   transform_expression structures fpdata expression3)
    | C.CAST (tp, init_expression) ->
       C.CAST (tp, transform_init_expression structures fpdata init_expression)     
    | C.CALL (expression, expression_list) ->
       begin
         let expression_list' = (transform_expression structures fpdata) |>>| expression_list in
         match expression with
         | (C.VARIABLE fname) as v 
           | C.PAREN ((C.VARIABLE fname) as v)
           | C.UNARY (C.MEMOF, ((C.VARIABLE fname) as v))
           | C.PAREN (C.UNARY (C.MEMOF, ((C.VARIABLE fname) as v)))
           ->
            begin
              match get_fpvar fpdata fname with
                Some (FPVAR d) ->
                 (* pw "FPVAR"; Cprint.print_expression ex; pw ""; *)
                 let ex' = try
                     build_conditional v expression_list' (sanitize |>>| d.to_funs)
                   with
                     Not_found -> pn "Not found in FPVAR"; raise Not_found
                 in
                 (* pw "==>"; Cprint.print_expression ex'; pn ""; *)
                 ex'
              | _ ->
                 C.CALL (transform_expression structures fpdata expression,
                         expression_list')
            end
         | C.INDEX _ as v
           | C.PAREN (C.INDEX _ as v)
           | C.UNARY (C.MEMOF, (C.INDEX _ as v))
           | C.PAREN (C.UNARY (C.MEMOF, (C.INDEX _ as v)))
           ->
            begin
              let ptr = get_arrptr expression in
              match get_fparr fpdata ptr with
                Some (FPARR d) ->
                 (* pw "FPARR"; Cprint.print_expression ex; pw ""; *)
                 let ex' = try
                     build_conditional v expression_list' (sanitize |>>| d.to_funs)
                 with
                   Not_found -> pn "Not found in FPARR"; raise Not_found
                 in
                 (* pw "==>"; Cprint.print_expression ex'; pn ""; *)
                 ex'
              | _ ->
                 C.CALL (transform_expression structures fpdata expression,
                         expression_list')
            end
         | _ ->
            begin
              
              let fpfld = get_fld_fp structures fpdata expression in
              match fpfld with
                Some (FPFLD d) ->
                 (* pw "FPFLD"; Cprint.print_expression ex; pw ""; *)
                 let ex' = try
                     build_conditional expression expression_list' (sanitize |>>| d.to_funs)
                 with
                   Not_found -> pn "Not found in FPFLD"; raise Not_found
                 in
                 (* pw "==>"; Cprint.print_expression ex'; pn ""; *)
                 ex'
              | _ -> 
                 C.CALL (transform_expression structures fpdata expression,
                         expression_list')
            end
         (* let matched_fpdata = fpcalls_in_expression fpdata expression in
         if List.length matched_fpdata > 0 then
           make_conditional expression expression_list' matched_fpdata
         else
           begin
             pn "No change";
             C.CALL (transform_expression fpdata expression,
                     expression_list')
           end *)
       end
    | C.COMMA expression_list ->
       C.COMMA ((transform_expression structures fpdata) |>>| expression_list)
    | C.CONSTANT constant ->
       expression
    | C.PAREN expression ->
       C.PAREN (transform_expression structures fpdata expression)
    | C.VARIABLE string ->
       expression
    | C.EXPR_SIZEOF expression ->
       C.EXPR_SIZEOF (transform_expression structures fpdata expression)
    | C.TYPE_SIZEOF _ ->
       expression
    | C.EXPR_ALIGNOF expression ->
       C.EXPR_ALIGNOF (transform_expression structures fpdata expression)
    | C.TYPE_ALIGNOF _ ->
       expression
    | C.INDEX (expression1, expression2) ->
       C.INDEX (transform_expression structures fpdata expression1,
                transform_expression structures fpdata expression2)
    | C.MEMBEROF (expression, fld) ->
       C.MEMBEROF (transform_expression structures fpdata expression, fld)
    | C.MEMBEROFPTR (expression, fld) ->
       C.MEMBEROFPTR (transform_expression structures fpdata expression, fld)
    | C.GNU_BODY block ->
       C.GNU_BODY (transform_block structures fpdata block)
    | C.EXPR_PATTERN _ ->
       expression

and transform_block structures fpdata block =
  { C.blabels = block.C.blabels;
    battrs = block.C.battrs;
    bstmts = (transform_statement structures fpdata) |>>| block.C.bstmts
  }

(* and transform_init_expression fpdata init_expression =
 *)
and transform_statement structures fpdata statement =
  match statement with
  | C.NOP _ ->
     statement
  | C.COMPUTATION (expression, cabsloc) ->
     C.COMPUTATION (transform_expression structures fpdata expression, cabsloc)
  | C.BLOCK (block, cl) ->
     C.BLOCK (transform_block structures fpdata block, cl)
  | C.SEQUENCE (statement1, statement2, cl) ->
     C.SEQUENCE (transform_statement structures fpdata statement1,
                 transform_statement structures fpdata statement2,
                 cl)
  | C.IF (expression, statement1, statement2, cl) ->
     let statement =
       C.IF (transform_expression structures fpdata expression,
           transform_statement structures fpdata statement1,
           transform_statement structures fpdata statement2,
           cl) in
     statement
  | C.WHILE (a, expression, statement, cl) ->
     let statement =
       C.WHILE (a,
                transform_expression structures fpdata expression,
                transform_statement structures fpdata statement,
                cl) in
     statement
  | C.DOWHILE (a, expression, statement, cl) ->
     let statement =
       C.DOWHILE (a, transform_expression structures fpdata expression,
                  transform_statement structures fpdata statement, cl)
     in
     statement
  | C.FOR (a, for_clause, expression1, expression2, statement, cl) ->
     let statement =
       C.FOR (a,
              transform_for_clause structures fpdata for_clause,
              transform_expression structures fpdata expression1,
              transform_expression structures fpdata expression2,
              transform_statement structures fpdata statement,
              cl)
     in
     statement
  | C.BREAK _ -> statement
  | C.CONTINUE _ -> statement
  | C.RETURN (expression, cl) ->
     C.RETURN (transform_expression structures fpdata expression, cl)
  | C.SWITCH (expression, statement, cl) ->
     let statement =
       C.SWITCH (transform_expression structures fpdata expression,
                 transform_statement structures fpdata statement, cl)
     in
     statement
  | C.CASE (expression, statement, cl) ->
     let statement =
       C.CASE (transform_expression structures fpdata expression,
               transform_statement structures fpdata statement, cl)
     in
     statement
  | C.CASERANGE (expression1, expression2, statement, cl) ->
     let statement =
       C.CASERANGE (transform_expression structures fpdata expression1,
                    transform_expression structures fpdata expression2,
                    transform_statement structures fpdata statement,
                    cl)
     in
     statement
  | C.DEFAULT (statement, cl) ->
     C.DEFAULT (transform_statement structures fpdata statement, cl)
  | C.LABEL (a, statement, cl) ->
     C.LABEL (a, transform_statement structures fpdata statement, cl)
  | C.GOTO _ -> statement
  | C.COMPGOTO (expression, cl) ->
     let statement = C.COMPGOTO (transform_expression structures fpdata expression, cl) in
     statement
  | C.DEFINITION definition ->
     C.DEFINITION (transform_definition structures fpdata definition)
  | C.ASM _ -> statement
  | C.TRY_EXCEPT (block1, expression, block2, cl) ->
     let statement =
       C.TRY_EXCEPT (transform_block structures fpdata block1,
                     transform_expression structures fpdata expression,
                     transform_block structures fpdata  block2,
                     cl)
     in
     statement
  | C.TRY_FINALLY (block1, block2, cl) ->
     C.TRY_FINALLY (transform_block structures fpdata block1,
                    transform_block structures fpdata block2, cl)

and transform_for_clause structures fpdata = function
    C.FC_EXP expression ->
    C.FC_EXP (transform_expression structures fpdata expression)
  | C.FC_DECL definition ->
     C.FC_DECL (transform_definition structures fpdata definition)

and transform_definition structures fpdata = function
    C.DECDEF ((specifier, init_name_list), cabsloc) ->
     let init_name_list' = (fun (name, init_expression) -> (name, transform_init_expression structures fpdata init_expression)) |>>| init_name_list in
     C.DECDEF ((specifier, init_name_list'), cabsloc)
  | definition -> definition

and transform_init_expression structures fpdata = function
    C.SINGLE_INIT expression ->
     C.SINGLE_INIT (transform_expression structures fpdata expression)
  | C.COMPOUND_INIT data ->
     let data' = (fun (initwhat, init_expression) -> (initwhat, transform_init_expression structures fpdata init_expression)) |>>| data in
     C.COMPOUND_INIT data'
  | init_expression -> init_expression

and transform_statement_by_if structures fpdata statement =
  match statement with
  | C.NOP _ ->
     statement
  | C.COMPUTATION (expression, cabsloc) ->
     transform_expression_by_if structures cabsloc fpdata expression statement
  | C.BLOCK (block, cl) ->
     C.BLOCK (transform_block structures fpdata block, cl)
  | C.SEQUENCE (statement1, statement2, cl) ->
     C.SEQUENCE (transform_statement_by_if structures fpdata statement1,
                 transform_statement_by_if structures fpdata statement2,
                 cl)
  | C.IF (expression, statement1, statement2, cl) ->
     let statement =   C.IF (expression,
           transform_statement_by_if structures fpdata statement1,
           transform_statement_by_if structures fpdata statement2,
           cl) in
     transform_expression_by_if structures cl fpdata expression statement
     
  | C.WHILE (a, expression, statement, cl) ->
     let statement =
       C.WHILE (a,
                expression,
                transform_statement_by_if structures fpdata statement,
                cl) in
     transform_expression_by_if structures cl fpdata expression statement
  | C.DOWHILE (a, expression, statement, cl) ->
     let statement =
       C.DOWHILE (a, expression,
                  transform_statement_by_if structures fpdata statement, cl)
     in
     transform_expression_by_if structures cl fpdata expression statement
  | C.FOR (a, for_clause, expression1, expression2, statement, cl) ->
     let matched_fpdata1 = fpcalls_in_expression structures fpdata expression1 in
     let matched_fpdata2 = fpcalls_in_expression structures fpdata expression2 in
     let matched_fpdata = matched_fpdata1 @@ matched_fpdata2 in
     let statement =
       C.FOR (a,
              for_clause,
              expression1,
              expression2,
              transform_statement_by_if structures fpdata statement,
              cl)
     in
     if List.length matched_fpdata > 0 then 
       (execute_transformation structures cl matched_fpdata) |->> (statement, matched_fpdata) 
     else
       statement
  | C.BREAK _ -> statement
  | C.CONTINUE _ -> statement
  | C.RETURN (expression, cl) ->
     transform_expression_by_if structures cl fpdata expression statement
  | C.SWITCH (expression, statement, cl) ->
     let statement =
       C.SWITCH (expression,
                 transform_statement_by_if structures fpdata statement, cl)
     in
     transform_expression_by_if structures cl fpdata expression statement
  | C.CASE (expression, statement, cl) ->
     let statement =
       C.CASE (expression,
               transform_statement_by_if structures fpdata statement, cl)
     in
     transform_expression_by_if structures cl fpdata expression statement
  | C.CASERANGE (expression1, expression2, statement, cl) ->
     let matched_fpdata1 = fpcalls_in_expression structures fpdata expression1 in
     let matched_fpdata2 = fpcalls_in_expression structures fpdata expression2 in
     let matched_fpdata = matched_fpdata1 @@ matched_fpdata2 in
     let statement =
       C.CASERANGE (expression1,
                    expression2,
                    transform_statement_by_if structures fpdata statement,
                    cl)
     in
     if List.length matched_fpdata > 0 then 
       (execute_transformation structures cl matched_fpdata) |->> (statement, matched_fpdata) 
     else
       statement
  | C.DEFAULT (statement, cl) ->
     C.DEFAULT (transform_statement_by_if structures fpdata statement, cl)
  | C.LABEL (a, statement, cl) ->
     C.LABEL (a, transform_statement_by_if structures fpdata statement, cl)
  | C.GOTO _ -> statement
  | C.COMPGOTO (expression, cl) ->
     let statement = C.COMPGOTO (expression, cl) in
     transform_expression_by_if structures cl fpdata expression statement
  | C.DEFINITION (C.DECDEF ((_,init_name_list),_)) ->
     if List.exists (fun (_, init_expression) ->
            match init_expression with
            | C.SINGLE_INIT (C.CALL (_, _)) -> true 
            | _ -> false
          ) init_name_list then
       raise (StError "Not supported definition")
     else
       statement
  | C.DEFINITION _ -> statement
  | C.ASM _ -> statement
  | C.TRY_EXCEPT (block1, expression, block2, cl) ->
     let statement =
       C.TRY_EXCEPT (transform_block structures fpdata block1,
                     expression,
                     transform_block structures fpdata  block2,
                     cl)
     in
     transform_expression_by_if structures cl fpdata expression statement
  | C.TRY_FINALLY (block1, block2, cl) ->
     C.TRY_FINALLY (transform_block structures fpdata block1,
                    transform_block structures fpdata block2, cl)

;;

let get_name_from_single_name (_, (name, _, _, _)) =
  name
;;

let fp_transform_function fpdata fname structures block =
  let fpdata' = (function FPVAR v -> v.in_fun = fname | FPFLD v -> v.in_fun = fname | FPARR v -> v.in_fun = fname) |>- fpdata in
  if List.length fpdata' > 0 then
    begin
      (* pn ("Transformed function: " ^ fname);
      pn "**************";
      iterS pp_ifptyp "\n" fpdata'; 
      pn "\n**************";
       Cprint.print_block block; *) 
      let block' = try
          transform_block structures fpdata' block
        with
          (* Not_found ->
          pn ("Not found in Function " ^ fname);
          raise Not_found *)
          _ -> exit(1)
      in
      (* pn "====>"; 
      Cprint.print_block block'; *) 
      block'
    end
  else
    block
;;

(*
let start_transform fpdata def =
  (** TODO: 1. Collect Function Pointer Typedef *)
  match def with
  | C.FUNDEF (single_name, block, cabsloc1, cabsloc2) ->
     (** TODO: 1. Collect parameters and their type *)
     let fname = get_name_from_single_name single_name in
     let block' = fp_transform_function fpdata fname block in in
     C.FUNDEF (single_name, block', cabsloc1, cabsloc2)
  | _ ->
     def;;

let transform_cabs (cabs : C.definition list) =
  let fpdata = get_fpdata () in
  let res = (start_transform fpdata) |>>| cabs in
  res
 *)
;;
