#!/bin/bash

PROJECT=$1
SVFDIR="/home/kmr/Dropbox/Work/Research/Project/SVF"
CURDIR=`pwd`
ANALYZER="$CURDIR/analyzer"
CLANG="/home/kmr/node_modules/llvm-10.0.0.obj/bin/clang"
WPA="$SVFDIR/Release-build/bin/wpa"

if [ $# -ne 1 ]; then
	echo "Function Pointer Eliminator for C"
    echo "Usage: ./fpe.sh <project-dir>"
	echo "This executes: "
	echo "(1) creates allfiles.bc by compiling all .c files under <project-dir> with clang"
	echo "(2) analyzes allfiles.bc by the driver program"	
    exit
fi

if [ ! -d $PROJECT ]; then
	echo "$PROJECT is not found"
	exit
fi

CURDIR=`pwd`
echo "ENTER $PROJECT"
cd $PROJECT

echo "DELETE old .bc files"
rm -f *.bc

echo "START: Making .bc files"
for CFILE in `find . -name '*.c'`
do
	echo "$CFILE"
	BCFILE=${CFILE%.*}.bc
	clang -c -fno-discard-value-names -emit-llvm $CFILE
	llvm-dis $BCFILE
done;
echo "FINISH: making .bc files"

echo "START: linking .bc files"
BCFILES=`find . -name '*.bc'`
llvm-link $BCFILES -o allfiles.bc

wpa -nander -dump-pag -dump-consG allfiles.bc

wpa -nander -dump-pag allfiles.bc

wpa -ander -dump-callgraph allfiles.bc


echo "FINISH: linking .bc files"			

echo "----------------"

time $ANALYZER allfiles.bc 2>&1 | tee ${CFILE%.*}.json

