BACKUPDIR="$1/SlacData"

[ -d "$BACKUPDIR" ] && echo "Deleting previous $BACKUPDIR"
[ -d "$BACKUPDIR" ] && rm -r $BACKUPDIR

mkdir $BACKUPDIR
mkdir "$BACKUPDIR/Parsed/"
mkdir "$BACKUPDIR/Translated/"
mkdir "$BACKUPDIR/Translated/func"
mkdir "$BACKUPDIR/Fpa"
mkdir "$BACKUPDIR/Fpa/GlobalData"
mkdir "$BACKUPDIR/Fpa/Fundef"
mkdir "$BACKUPDIR/Fpa/Profiles"
mkdir "$BACKUPDIR/Translated/Compacted"
mkdir "$BACKUPDIR/Translated/FPTransformed"

echo "Start Parsing"
./slac-parser $1  
echo "End Parsing"

fns=`ls $BACKUPDIR/Parsed/`
#./slac-init $BACKUPDIR/Translated
number=0
for i in $fns
do
		echo "$number"
		echo $BACKUPDIR/Parsed/$i
		#		./slac-unit $BACKUPDIR/Translated $BACKUPDIR/Parsed/$i $number
		./slac-unit $BACKUPDIR $BACKUPDIR/Parsed/$i $number $2 -deb $3 
		number=`echo "$number + 1" | bc`
done

./fpa-preprocess $BACKUPDIR
