#!/bin/bash

FPEdir=`pwd`
SVFdir="$FPEdir/SVF"
ANALYZER="$FPEdir/analyzer"
WPA="$SVFdir/Release-build/bin/wpa"

function myMessage {
	echo "FPE - Function Pointer Eliminator for C"
	echo ""
	echo "Usage: fpe.sh <dir> [options]"
	echo "where <dir> contains C preprocessed files and sub directories."
	echo ""
	echo "Description:"		
	echo "The command creates a new directory <dir>-fpe that contains"
	echo "C files without function pointer calls in the same subdirectories."
}

if [ $# -ne 1 ]
then
   myMessage
   exit
fi

PROJECT=$(cd $1 && pwd) # project (in full path)

if [ ! -d $PROJECT ]
then
	echo "$PROJECT is not found"
	exit
fi

echo "Project directory"
echo $PROJECT
echo ""

BCFILES=`find $PROJECT -name '*\.bc'`
if [ -n "$BCFILES" ]
then
	echo ">> Old bitcode files exist --> Delete"
	for BCFILE in $BCFILES
	do
		rm -f $BCFILE
	done
	echo ">> Done"	
fi

echo ">> Begin: making bitcode files"
for CFILE in `find $PROJECT -name '*.c'`
do
	echo "$CFILE"
	BCFILE=${CFILE%.*}.bc
	clang -c -fno-discard-value-names -emit-llvm $CFILE -o $BCFILE
#	llvm-dis $BCFILE
done;
echo ">> End: making bitcode files"

echo ">> Begin: linking bitcode files"
BCFILES=`find $PROJECT -name '*\.bc'`
echo $PROJECT/allfiles.bc
cd $PROJECT
llvm-link -o $PROJECT/allfiles.bc $BCFILES
echo ">> End: linking bitcode files --> allfiles.bc is created"
echo ""

echo ">> Begin: Function Pointer Analysis"
# $WPA -nander allfiles.bc
# $WPA -nander -dump-pag allfiles.bc
echo $PROJECT/allfiles.bc
function execAnalyzer {
	#	time $ANALYZER $PROJECT/allfiles.bc 2>&1 | tee $PROJECT/fpe-output.json
	$ANALYZER $PROJECT/allfiles.bc > $PROJECT/fpe-output.json	
}
function myFail {
	echo "---------"
	echo "FPE failed"
	exit
}
time execAnalyzer || myFail
echo ">> End: Function Pointer Analysis"

echo ">> Begin: Program Transformation"
cd $FPEdir/slac
echo $PROJECT
echo $PROJECT/fpe-output.json
time ./gen.sh $PROJECT $PROJECT/fpe-output.json
echo ">> End: Program Transformation"
echo ">> Output results: $PROJECT-FPE"
echo "---------"
echo "FPE finished"



