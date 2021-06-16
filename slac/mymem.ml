
let getMemSize () =
  let memSize line : int =
    (* Lines should be in the form "MemTotal:        8061780 kB" *)
    let len = Bytes.length line in
    let charlist = ref [] in
    for i = 0 to len - 1 do
      let c = Bytes.get line i in
      if '0' <= c && c <= '9'
      then
        charlist := !charlist @ [c]
      else
        ()
    done;
    let n = List.length !charlist in
    let memsize = Bytes.create n in
    for i = 0 to n - 1 do
      Bytes.set memsize i (List.nth !charlist i)
    done;
    (int_of_string memsize)/1000
  in
  let sz_MemTotal = ref 0 in
  let sz_MemFree = ref 0 in
  let sz_Buffers = ref 0 in
  let sz_Cached = ref 0 in
  let sz_SReclaimable = ref 0 in
  let line = ref "" in
  let ic = open_in "/proc/meminfo" in
  for i = 0 to 22 do
    line := input_line ic;
    match Bytes.sub !line 0 5 with
    | "MemTo" -> sz_MemTotal := memSize !line
    | "MemFr" -> sz_MemFree := memSize !line
    | "Buffe" -> sz_Buffers := memSize !line
    | "Cache" -> sz_Cached := memSize !line
    | "SRecl" -> sz_SReclaimable := memSize !line
    | _ -> ()
  done;
  close_in ic;
  let sz_buffcache = !sz_Buffers + !sz_Cached + !sz_SReclaimable in
  let sz_used = !sz_MemTotal - !sz_MemFree - sz_buffcache in
  (!sz_MemTotal,sz_used,!sz_MemFree)
;;

let show_current_used_memsize counter mes =
  let (_,sz_used,_) = getMemSize () in
  print_endline @@ "Used Mem: " ^ (string_of_int sz_used) ^ "mb " ^ mes ^ (string_of_int counter)
  
