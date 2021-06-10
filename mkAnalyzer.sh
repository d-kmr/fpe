#!/bin/bash

SVF_DIR="/home/kmr/Dropbox/Work/Research/Project/SVF"
SVF_HEADER="$SVF_DIR/include"

LLVM_DIR="$SVF_DIR/llvm-10.0.0.obj"
LLVM_INCLUDE_DIRS="$LLVM_DIR/include"

SVF_LIB_DIR="$SVF_DIR/Release-build/lib"
LLVM_LIB_DIR="$LLVM_DIR/lib"

g++ -I$LLVM_INCLUDE_DIRS -I$SVF_HEADER -fPIC -std=gnu++14 -O3 -fno-rtti -Wno-deprecated   -D_GNU_SOURCE -D__STDC_CONSTANT_MACROS -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -std=gnu++14 -o analyzer.o -c analyzer.cpp

g++ -fPIC -std=gnu++14 -O3 -fno-rtti -Wno-deprecated analyzer.o -o analyzer $SVF_LIB_DIR/libSvf.a $SVF_LIB_DIR/CUDD/libCudd.a $LLVM_LIB_DIR/libLLVMBitWriter.a $LLVM_LIB_DIR/libLLVMCore.a $LLVM_LIB_DIR/libLLVMipo.a $LLVM_LIB_DIR/libLLVMIRReader.a $LLVM_LIB_DIR/libLLVMInstCombine.a $LLVM_LIB_DIR/libLLVMInstrumentation.a $LLVM_LIB_DIR/libLLVMTarget.a $LLVM_LIB_DIR/libLLVMLinker.a $LLVM_LIB_DIR/libLLVMAnalysis.a $LLVM_LIB_DIR/libLLVMScalarOpts.a $LLVM_LIB_DIR/libLLVMSupport.a $LLVM_LIB_DIR/libLLVMBitWriter.a $LLVM_LIB_DIR/libLLVMAsmParser.a $LLVM_LIB_DIR/libLLVMInstCombine.a $LLVM_LIB_DIR/libLLVMAggressiveInstCombine.a $LLVM_LIB_DIR/libLLVMVectorize.a $LLVM_LIB_DIR/libLLVMTransformUtils.a $LLVM_LIB_DIR/libLLVMAnalysis.a $LLVM_LIB_DIR/libLLVMObject.a $LLVM_LIB_DIR/libLLVMBitReader.a $LLVM_LIB_DIR/libLLVMMCParser.a $LLVM_LIB_DIR/libLLVMTextAPI.a $LLVM_LIB_DIR/libLLVMProfileData.a $LLVM_LIB_DIR/libLLVMCore.a $LLVM_LIB_DIR/libLLVMRemarks.a $LLVM_LIB_DIR/libLLVMBitstreamReader.a $LLVM_LIB_DIR/libLLVMMC.a $LLVM_LIB_DIR/libLLVMBinaryFormat.a $LLVM_LIB_DIR/libLLVMDebugInfoCodeView.a $LLVM_LIB_DIR/libLLVMDebugInfoMSF.a $LLVM_LIB_DIR/libLLVMSupport.a -lrt -ldl -ltinfo -lpthread -lm $LLVM_LIB_DIR/libLLVMDemangle.a 

