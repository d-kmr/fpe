#!/bin/bash

FPEdir=$(pwd)
sysOS=`uname -s`
SVFgit="https://github.com/SVF-tools/SVF.git"
SVFdir="$FPEdir/SVF"
SVFheader="$SVFdir/include"
SVFlib="$SVFdir/Release-build/lib"

if [ $# = 0 ]
then
	echo "Usage: fpebuild.sh [make|remake|clean]"
	echo "[Options]"
	echo "make  : compile fpe installing SVF"
	echo "remake: clean all and recompile fpe and SVF"	
	echo "clean : delete SVF directory and other object files"
	exit
fi   

if [[ $1 = "clean" ]] || [[ $1 = "remake" ]]
then
	echo "Deleting SVF directory and .o files ..."
	rm -fr $SVFdir
	rm -f *.o
	echo "Done"
	if [[ $1 = "clean" ]]
	then
		exit
	fi
fi

echo "SVF checking ..."
SVFinstalled=0
if [ -d $SVFdir ]
then
	echo "$SVFdir exists"
	SVFinstalled=1
else
	echo "$SVFdir does not exist"
fi   

# SVF installation
if [[ $SVFinstalled = 0 ]] 
then
	echo "Start building of SVF"	
	echo "git cloning"
	git clone $SVFgit
	echo "Patching to suppress output for FPE"
	patch SVF/lib/Util/PTAStat.cpp patchfile
	echo "cd SVF"	
	cd SVF
	echo "build SVF"
	source ./build.sh
fi

# Analyzer building
echo "cd fpe"
cd $FPEdir
echo "Compiling analyzer"
if [[ $LLVM_DIR = "" ]]
then
   LLVM_DIR="$SVFdir/llvm-12.0.0.obj"
fi   
LLVMinclude="$LLVM_DIR/include"
LLVMlib="$LLVM_DIR/lib"
echo "LLVM_DIR = $LLVM_DIR"
echo "LLVMinclude = $LLVMinclude"
echo "SVFheader = $SVFheader"
g++ -I$LLVMinclude -I$SVFheader -fPIC -std=gnu++14 -O3 -fno-rtti -Wno-deprecated -D_GNU_SOURCE -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -o analyzer.o -c analyzer.cpp

g++ -fPIC -std=gnu++14 -O3 -fno-rtti -Wno-deprecated analyzer.o -o analyzer $SVFlib/libSvf.a $SVFlib/CUDD/libCudd.a $LLVMlib/libLLVMBitWriter.a $LLVMlib/libLLVMCore.a $LLVMlib/libLLVMipo.a $LLVMlib/libLLVMIRReader.a $LLVMlib/libLLVMInstCombine.a $LLVMlib/libLLVMInstrumentation.a $LLVMlib/libLLVMTarget.a $LLVMlib/libLLVMLinker.a $LLVMlib/libLLVMAnalysis.a $LLVMlib/libLLVMScalarOpts.a $LLVMlib/libLLVMSupport.a $LLVMlib/libLLVMBitWriter.a $LLVMlib/libLLVMAsmParser.a $LLVMlib/libLLVMInstCombine.a $LLVMlib/libLLVMAggressiveInstCombine.a $LLVMlib/libLLVMVectorize.a $LLVMlib/libLLVMTransformUtils.a $LLVMlib/libLLVMAnalysis.a $LLVMlib/libLLVMObject.a $LLVMlib/libLLVMBitReader.a $LLVMlib/libLLVMMCParser.a $LLVMlib/libLLVMTextAPI.a $LLVMlib/libLLVMProfileData.a $LLVMlib/libLLVMCore.a $LLVMlib/libLLVMRemarks.a $LLVMlib/libLLVMBitstreamReader.a $LLVMlib/libLLVMMC.a $LLVMlib/libLLVMBinaryFormat.a $LLVMlib/libLLVMDebugInfoCodeView.a $LLVMlib/libLLVMDebugInfoMSF.a $LLVMlib/libLLVMSupport.a -lrt -ldl -ltinfo -lpthread -lz -lm $LLVMlib/libLLVMDemangle.a 
echo "Done"
