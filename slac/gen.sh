echo "Transformation begins"
PWD=`pwd`

PROJECT=$1

if [ ${PROJECT:0:1} != "/" ]
then
		PROJECT="$PWD/$PROJECT"
fi

if [ ${PROJECT:${#PROJECT}-1} = "/" ]
then
		PROJECT=${PROJECT:0:${#PROJECT}-1}
fi

FPJSON=$2
if [ ${FPJSON:0:1} != "/" ]
then
		FPJSON="$PWD/$FPJSON"
fi

FPEDIR="${PROJECT}-FPE/"



[ -d "$FPEDIR" ] || mkdir "$FPEDIR"

END=${#PROJECT}+1


Transform(){
		CURDIR=$1
		ABSDIR=$PROJECT/$CURDIR
		NEWDIR=$FPEDIR$CURDIR
		
		t=`ls $ABSDIR*.c 2> /dev/null`
		for i in $t
		do
				FILE=${i:${#ABSDIR}}
				DEST="$NEWDIR$FILE"
				./fpe-parser "$i" "${DEST}abs" "$FILE"
				./fpe-unit "${DEST}abs" "$FPJSON" > "${DEST}"
				rm "${DEST}abs"
		done

		t=`ls -d $ABSDIR*/ 2> /dev/null`
		for j in $t
		do
				DIR=${j:$END}
				[ -d "$FPEDIR$DIR" ] || mkdir "$FPEDIR$DIR"
				Transform $DIR
		done
				
}

Transform "" 

echo "Transformation is finished"
