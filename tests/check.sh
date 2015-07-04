#!/bin/sh

INFILE=$1
EXT=.ch
OUTFILE=${INFILE%$EXT}.out

TMPFILE=$(tempfile -d . -s .out)

CHARIOT=../main.native


trap "rm -f $TMPFILE; exit $EXIT_STATUS" INT TERM EXIT


echo -n "file $INFILE ... \t"
$CHARIOT $INFILE > $TMPFILE 2>&1

if [ -f $OUTFILE ]
then
    DIFF=$(diff $OUTFILE $TMPFILE)
    if [ $? -eq 0 ]
    then
        echo "OK"
    else
        echo "OOPS, the output is different from the recorded one:"
        echo "$DIFF"
        while true
        do
            echo -n "accept new output? "
            read -p "[yN] " R
            case $R in
                y | Y )
                    mv $TMPFILE $OUTFILE
                    echo "replaced old output by new..."
                    EXIT_STATUS=0
                    break
                ;;
                n | N | "" )
                    echo "ERROR... Unexpected output"
                    EXIT_STATUS=1
                    break
                ;;
                * )

            esac
        done
    fi
else
    echo
    echo "no output file found"
    echo "Is the following correct?"
    cat $TMPFILE
    while true
    do
        read -p "[Yn] " R
        case $R in
            y | Y | "")
                mv $TMPFILE $OUTFILE
                echo "result saved in $OUTFILE"
                EXIT_STATUS=0
                break
            ;;
            n | N )
                echo "no result saved"
                EXIT_STATUS=1
                break
            ;;
            *)
        esac
    done
fi


rm -f $TMPFILE

exit $EXIT_STATUS



