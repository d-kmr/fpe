#!/bin/bash

FPEdir=`pwd`
PROJECT=$1
SVFdir="$FPEdir/SVF"
ANALYZER="$FPEdir/analyzer"
WPA="$SVFdir/Release-build/bin/wpa"

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

echo "Enter $PROJECT"
cd $PROJECT

echo "DELETE old .bc files"
rm -f *.bc

echo "START: Making .bc files"
for CFILE in `find . -name '*.c'`
do
	echo "$CFILE"
	BCFILE=${CFILE%.*}.bc
	clang -c -fno-discard-value-names -emit-llvm $CFILE
	llvm-dis-11 $BCFILE
done;
echo "FINISH: making .bc files"

echo "START: linking .bc files"
BCFILES=`find . -name '*.bc'`
llvm-link-11 $BCFILES -o allfiles.bc

#$WPA -nander -dump-pag -dump-consG allfiles.bc
$WPA -nander allfiles.bc
$WPA -nander -dump-pag allfiles.bc

$WPA -ander -dump-callgraph allfiles.bc


echo "FINISH: linking .bc files"			

echo "----------------"
echo $PROJECT${CFILE%.*}.json

time $ANALYZER allfiles.bc 2>&1 | tee ${CFILE%.*}.json

cd $FPEdir/slac
time ./slac-gen.sh $PROJECT $PROJECT${CFILE%.*}.json
