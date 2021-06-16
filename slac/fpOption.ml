
let _startfunc = ref "main"
;;

module Option = struct

  type t =
	{
	  mutable debug : bool; (* flag for debug mode *)
	}

  let o =
	{
	  debug = false;
	}

  let debugFlag () = o.debug
	  
  let setDebug () = o.debug <- true
  let unsetDebug () = o.debug <- false
	
  let doIfDebug f arg = if o.debug then f arg else ()

  let doIfDebugLazy f argfun = if o.debug then f (argfun ()) else ()
	  
  let sayIfDebug mes = 
	let f () = print_endline mes in
	doIfDebug f ()

  let sayIfDebug0 mes =
	let f () = print_string mes in
	doIfDebug f ()

  let sayIfDebugLazy mesfun =
    if o.debug then
      let mes = mesfun () in
	  let f () = print_endline mes in
	  doIfDebug f ()
    else ()

  let sayIfDebug0Lazy mesfun =
    if o.debug then
      let mes = mesfun () in
	  let f () = print_string mes in
	  doIfDebug f ()
    else ()

    
  let debugPrompt = "==> "

end
;;
