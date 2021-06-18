#!/bin/tcsh -f                                                                                                                                                              

set OCAMLLIBS = "nums.cmxa unix.cmxa z3ml.cmxa"
set LIBDIR = "lib"
#set SOURCES = "ftools.ml tools.ml mymem.ml ctransformOptions.ml ctransform.ml slsyntax.ml smtsyntax.ml smttoz3.ml entlcheck.ml entlcheck_b.ml biabd.ml interval.ml psimp.ml vcpBase.ml vcpTranslate.ml convFtoK.ml vcpVBase.ml  vcpUnfoldVerify.ml vcpAllC.ml vcpPrecond2.ml vcpLib.ml vcp.ml"
set SOURCES = "ftools.ml mymem.ml vcpBase.ml bignum.ml smtsyntax.ml smttoz3.ml sltosmt.ml satcheck.ml interval.ml entlcheckA.ml biabdls.ml biabd.ml vcpExtract.ml ctransformOptions.ml ctransform.ml csyntax.ml vcpFpOnC.ml vcpTranslate.ml vcpElements.ml vcpDep.ml vcpAllC.ml fpOption.ml fpsyntax3.ml fp3.ml convFtoK.ml vcpVBase.ml vcpBuiltIn.ml vcpPrecond2.ml vcpLib.ml"
set TRANS = "ftools.ml vcpBase.ml bignum.ml vcpExtract.ml ctransformOptions.ml ctransform.ml vcpFpOnC.ml vcpTranslate.ml csyntax.ml vcpElements.ml vcpAllC.ml"
set TRANSCMXS = "ftools.cmx vcpBase.cmx bignum.cmx vcpExtract.cmx ctransformOptions.cmx ctransform.cmx vcpFpOnC.cmx vcpTranslate.cmx csyntax.cmx vcpElements.cmx vcpAllC.cmx"
set UCMXS = "pretty.cmx cabs.cmx errormsg.cmx longarray.cmx growArray.cmx cabshelper.cmx lexerhack.cmx escape.cmx whitetrack.cmx cprint.cmx stats.cmx cparser.cmx clexer.cmx frontc.cmx tools.cmx slsyntax.cmx manualinput_lexer.cmx manualinput_parser.cmx manualinput.cmx"
set CMXS = "ftools.cmx mymem.cmx vcpBase.cmx bignum.cmx smtsyntax.cmx smttoz3.cmx sltosmt.cmx satcheck.cmx interval.cmx entlcheckA.cmx biabdls.cmx biabd.cmx vcpExtract.cmx ctransformOptions.cmx ctransform.cmx vcpFpOnC.cmx vcpTranslate.cmx vcpElements.cmx csyntax.cmx vcpDep.cmx vcpAllC.cmx fpOption.cmx fpsyntax3.cmx fp3.cmx convFtoK.cmx vcpVBase.cmx vcpBuiltIn.cmx vcpPrecond2.cmx vcpLib.cmx"
set CMIS = "tools.cmi bignum.cmi ctransformOptions.ml ctransform.ml slsyntax.cmi smtsyntax.cmi smttoz3.cmi interval.cmi manualinput.cmi"
set TARGET = "slac.native"


ocamlopt -c pretty.ml
ocamlopt -c cabs.ml
ocamlopt -c errormsg.ml
ocamlopt -c longarray.ml
ocamlopt -c growArray.ml
ocamlopt -c cabshelper.ml
ocamlopt -c lexerhack.ml
ocamlopt -c escape.ml
ocamlopt -c whitetrack.ml
ocamlopt -c cprint.ml
ocamlopt -c stats.ml
ocamlopt -c trace.ml

ocamllex clexer.mll
ocamlopt -c cparser.mli
ocamlyacc cparser.mly
ocamlopt -c cparser.ml
ocamlopt -c clexer.ml

ocamlopt -c frontc.ml

ocamlopt -c tools.ml slsyntax.ml 
ocamllex manualinput_lexer.mll
ocamlyacc manualinput_parser.mly
ocamlopt -c manualinput_parser.mli
ocamlopt -c manualinput_lexer.ml manualinput_parser.ml manualinput.ml


#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "slac-parser" -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $TRANS "slacParser.ml"
ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "fpe-parser" -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $TRANS "fpeParser.ml"
ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "fpe-unit" -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $SOURCES "fpeUnit.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "slac-unit" -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $SOURCES "slacUnit.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "fpa-preprocess" -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "fpaPreprocess.ml"
##ocamlopt -o "fpa-deplist" -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "fpaDepList.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o $TARGET -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "vcp.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "read-fpaProfile"  -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "readFpaProfile.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "read-fpaFuntable"  -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "readFpaFuntable.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "read-fpaGlobalData"  -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "readFpaGlobalData.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "read-fpaSH"  -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "readFpaSH.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg -bin-annot -o "read-module"  -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $TRANSCMXS "readModule.ml"
#ocamlfind ocamlopt -package ppx_deriving_yojson -linkpkg  -bin-annot -o "slac-init"  -I $LIBDIR -cclib "-L. -lz3" $OCAMLLIBS $UCMXS $CMXS "slacInit.ml"
