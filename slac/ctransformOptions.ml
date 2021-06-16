
let debugFlag = ref false;;

let unsetDebug () = debugFlag := false;;

let setDebug () = debugFlag := true;;
  
let doIfDebug f x = if !debugFlag then f x else ()

let doIfDebugLazy f arg = if !debugFlag then f (arg ()) else ()

