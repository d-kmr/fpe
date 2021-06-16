open Ftools

module CallGraph = struct
  type t = (bytes, bytes list) Hashtbl.t

  let create ls : t =
    let tbl = Hashtbl.create 100 in
    List.iter (fun (k, v) -> Hashtbl.replace tbl k v) ls;
    tbl

  let transpose tbl =
    let tbl2 = Hashtbl.create 100 in
    let init v =
      if not (Hashtbl.mem tbl2 v) then
        Hashtbl.add tbl2 v []
    in
    Hashtbl.iter (fun u vl ->
        init u;
        List.iter (fun v ->
            let ul = try Hashtbl.find tbl2 v
                     with _ -> []
            in
            Hashtbl.replace tbl2 v (u :: ul)
          ) vl 
      ) tbl;
    tbl2
end

let add_missing_nodes graph_l graph =
  (**
     Initially,
     missing = {(v, []) | (_, vl) `in` graph_l, v `in` vl, v `notin` graph}
   *)
  let missing : (bytes * bytes list) list =
    List.fold_left (fun acc (_, vl) ->
        List.fold_left (fun acc v ->
            if not (Hashtbl.mem graph v) then
              (v, [])::acc
            else
              acc
          ) acc vl
      ) [] graph_l
    |> List.rev
  in
  (**
     impure update to graph
     {(y1,[]);(y2,[])} -->
     <y1-->[]
      y2-->[]>

      
   *)
  List.iter (fun (v,vl) -> Hashtbl.replace graph v vl) missing;
  (**
     {(x,[y1;y2])} -->
     {(x,[y1;y2]);(y1,[]);(y2,[])}
   *)
  graph_l @ missing
;;

let partition graph_l =
  let graph = CallGraph.create graph_l in
  let graph_l = add_missing_nodes graph_l graph in
  (** check if graph = graph_tr *)
  let graph_tr = CallGraph.transpose graph in
  let visits = Hashtbl.create 100 in
  let is_visited v = Hashtbl.mem visits v in
  let mark_visited v = Hashtbl.replace visits v () in
  let get_out_neighbors v =
    try Hashtbl.find graph v
    with Not_found -> assert false
  in
  let get_in_neighbors v =
    try Hashtbl.find tr_graph v
    with Not_found -> assert false
  in
  let rec visit acc v =
    if not (is_visited v) then (
      mark_visited v;
      let out_neighbors = get_out_neighbors v in
      let acc =
        List.fold_left (fun acc u -> visit acc u) acc out_neighbors in
      v :: acc
    )
    else
      acc
  in
  let l =
    List.fold_left (fun acc (v, _vl) ->
        visit acc v
      ) [] graph_l
  in
  let assignments = Hashtbl.create 100 in
  let is_assigned v = Hashtbl.mem assignment v in
  let rec assign v root =
    if not (is_assigned v) then
      Hashtbl.replace
  in
  ()
