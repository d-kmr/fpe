open VcpTranslate
open VcpBase
open Ftools
 

let procs : (((bytes * Var.attr list) * Block.t list * Block.t) * Formula.t * Formula.t) list ref = ref []

let s = ref 0;;

let i_s = ref true

let reset p =
  procs.contents <- p;
  s.contents <- 0;
  i_s.contents <- true


let rec get_branches = function
  | Block.SKIP ->
    (0, Big_int.unit_big_int)
  | Block.ASSIGN (a, b, z, l) -> get_branches z
  | Block.ASSERT (a, z, l) -> get_branches z
  | Block.IF (a, b, c, z, l) ->
(*    let b = Block.compose z b in
      let c = Block.compose z c in *)
    let (y1, x1) = get_branches b in
    let (y2, x2) = get_branches c in
    let (y, x)  = get_branches z in
    let y = y + (if y1 > y2 then y1 else y2) in 
    (y+1, Big_int.mult_big_int x (Big_int.add_big_int x1 x2))
  | Block.WHILE (a, b, c, z, l) ->
    (* let b = Block.compose z b in *)
    let (y, x)  = get_branches z in 
    let (y1,x1) = get_branches b in
    y+y1+1, Big_int.mult_big_int x (Big_int.succ_big_int x1)
  | Block.PROCCALL (str, args, body, l) -> 
    begin  
      match body with
        Block.ASSIGN (v1, e1, b1, l1) when l = l1 -> 
        let (is_ptr, is_struct, type_name) = 
          try
            let ((name, param_statements, _), pre1, post1) = 
              List.find (fun ((name, _, _), _, _) -> Var.toStr name = str) !procs in
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
              get_branches body
            else
              get_branches body
          | true, false ->
            let nv = newvar () in
            let attr = Var.get_attributes v1 in
            let body =
              Block.PARALLEL(
                Block.ASSIGN (v1, Term.NULL, Block.SKIP, l),
                Block.MAPS (v1, (nv, attr), Block.SKIP, l),
                b1,
                l)
            in
            get_branches body
          | false, true ->
            let (_, fields) = List.find (fun (n, _) -> n = type_name) (!Block.structures) in
            let body = Block.CONS (Exp.VAR v1, (fun (ns, e) -> (Bytes.concat "." ns, e)) |>>| fields, b1, l) in
            get_branches body
          | false, false ->
            let nv = newvar () in
            let attr = Var.get_attributes v1 in
            let body = Block.ASSIGN (v1, Term.encode (nv, attr), b1, l) in
            get_branches body
        end
      | _ -> get_branches body
    end
  | Block.CONS (a, b, z, l) ->
    get_branches z
  | Block.MUTATION (a, b, c, z, l) -> get_branches z
  | Block.LOOKUP (a, b, c, z, l) -> get_branches z 
  | Block.DISPOSE (a, z, l) -> get_branches z
  | Block.ARRAY (a, b, tl, z, l) -> get_branches z 
  | Block.PARALLEL (b, c, z, l) ->
    let (y, x) = get_branches z in
    y+1, Big_int.mult_big_int (Big_int.big_int_of_int 2) x 
  | Block.MAPS (a, b, z, l) -> get_branches z 



