#!/bin/bash

NUM_PROCESSES=3

set -x

BASENAME=`basename $0`
PROPERTY=${BASENAME%.sh}
ORIG_PROPERTY=${PROPERTY}

case ${PROPERTY} in
mb*)
    FILENAME=mailboxes-test.pml
    SPIN_OPTIONS=
    ONE_BROADCASTER=0
    ;;
rb*)
    FILENAME=broadcast-test.pml
    SPIN_OPTIONS="-DRELIABLE_BROADCAST"
    ONE_BROADCASTER=1
    PROPERTY=${PROPERTY#rb_}
    ;;
bb*)
    FILENAME=broadcast-test.pml
    SPIN_OPTIONS=
    PROPERTY=${PROPERTY#bb_}
    ONE_BROADCASTER=0
    ;;
*)
    echo "Invalid filename"
    exit 1
esac

TRAILNAME=${FILENAME}.trail

function run {
    rm ${TRAILNAME}
    spin $1 -a ${FILENAME}
    gcc -DNOREDUCE -DQUADCORE -O2 pan.c -o pan
    ./pan -E -a -N ${PROPERTY}

    if [ -f ${TRAILNAME} ]
    then
        cp ${TRAILNAME} ../trail/${ORIG_PROPERTY}.trail
        echo "$1" > ../trail/${ORIG_PROPERTY}.spin-options
        exit 42
    fi
}

pushd src

for ((i=1;i<=NUM_PROCESSES;i++))
do
    for ((j=1;j<=NUM_PROCESSES;j++))
    do
        for ((k=1;k<=NUM_PROCESSES;k++))
        do
            OPTIONS="-DNUM_PROCESSES=${NUM_PROCESSES} ${SPIN_OPTIONS} -DSENDER=${i} -DRECEIVER=${j} -DTHIRD=${k}"
            if [ ${ONE_BROADCASTER} -ne 0 ]
            then
                OPTIONS="${OPTIONS} -DONE_BROADCASTER=${i}"
            fi
            run "${OPTIONS}"
        done
    done
done

popd
