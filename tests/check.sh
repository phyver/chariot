#!/bin/sh

EXT=.ch

INTERACTIVE=1

INDENT="  "

USAGE=$(cat <<EOS
usage:
  $0 [-i] [-n] <file>
    -i      run interactively (default)
    -n      run non-interactively, with minimal output
  file should have extension $EXT
EOS
)

while getopts "ni" f
do
    case $f in
        n)  INTERACTIVE=0           ;;
        i)  INTERACTIVE=1           ;;
        \?) echo "$USAGE"; exit 3     ;;
    esac
done
shift `expr $OPTIND - 1`


INFILE=$1

case $INFILE in
    *$EXT ) ;;
    *)
    echo "ERROR... bad extension"
    exit 1
    ;;
esac

OUTFILE=${INFILE%$EXT}.out

TMPFILE=${INFILE%$EXT}.tmpout

CHARIOT=../main.native

# DIFF_PRG="diff -y"
# DIFF_PRG="git diff --color-words --no-index"
DIFF_PRG="git diff --color --word-diff=plain --no-index"

# trap "rm -f $TMPFILE; exit $EXIT_STATUS" INT TERM EXIT

message() {
    if [ "$INTERACTIVE" = "0" ]
    then
        :       #NOP
    else
        echo "$@"
    fi
}

message -n "${INDENT}file $INFILE ... \t"
$CHARIOT $INFILE > $TMPFILE

if [ -f $OUTFILE ]
then
    DIFF=$($DIFF_PRG $OUTFILE $TMPFILE)
    if [ -z "$DIFF" ]
    then
        message "OK"
    else
        message "OOPS, the output is different from the recorded one:"
        if [ "$INTERACTIVE" = "0" ]
        then
            echo "$INFILE: output different from the recorded one..."
            rm -f $TMPFILE
            EXIT_STATUS=1
            exit $EXIT_STATUS
        fi
        message "$DIFF"
        while true
        do
            message -n "accept new output? "
            read -p "[yNc] " R
            case $R in
                y | Y )
                    mv $TMPFILE $OUTFILE
                    message "replaced old output by new..."
                    EXIT_STATUS=0
                    break
                ;;
                n | N | "" )
                    message "ERROR... Unexpected output"
                    EXIT_STATUS=1
                    break
                ;;
                c | C )
                    message "old result kept"
                    message "continue anyway"
                    EXIT_STATUS=0
                    break
                ;;
                * )

            esac
        done
    fi
else
    message
    message "no output file found"
    if [ "$INTERACTIVE" = "0" ]
    then
        echo "$INFILE: no output file found"
        rm -f $TMPFILE
        EXIT_STATUS=1
        exit $EXIT_STATUS
    fi
    message "Is the following correct?"
    cat $TMPFILE
    while true
    do
        read -p "[Ync] " R
        case $R in
            y | Y | "")
                mv $TMPFILE $OUTFILE
                message "result saved in $OUTFILE"
                EXIT_STATUS=0
                break
            ;;
            n | N )
                message "no result saved"
                EXIT_STATUS=1
                break
            ;;
            c | C )
                message "no result saved"
                message "continue anyway"
                EXIT_STATUS=0
                break
            ;;
            *)
        esac
    done
fi


rm -f $TMPFILE

exit $EXIT_STATUS



