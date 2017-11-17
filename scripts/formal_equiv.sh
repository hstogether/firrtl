#!/usr/bin/env bash
# This script is for formally comparing the Verilog emitted by different git revisions
# There must be two valid git revision arguments
set -e

if [ $# -ne 2 ]; then
    echo "There must be exactly two arguments!"
    exit -1
fi

HASH1=`git rev-parse $1`
HASH2=`git rev-parse $2`

echo "Comparing git revisions $HASH1 and $HASH2"

if [ $HASH1 = $HASH2 ]; then
    echo "Both git revisions are the same! Nothing to do!"
    exit 0
fi

RET=""
make_verilog () {
    git checkout $1
    local filename="rob.$1.v"

    sbt clean
    sbt "run-main firrtl.Driver -i regress/Rob.fir -o $filename -X verilog"
    RET=$filename
}

# Generate Verilog to compare
make_verilog $HASH1
FILE1=$RET

make_verilog $HASH2
FILE2=$RET

stayin_alive () {
  while true; do
    echo -n "."
    sleep 10
  done
}

echo "Comparing $FILE1 and $FILE2"

if cmp -s $FILE1 $FILE2; then
    echo "File contents are identical!"
    exit 0
else
    echo "Running equivalence check using Yosys"
    stayin_alive &
    yosys -q -p "
      read_verilog $FILE1
      rename Rob top1
      read_verilog $FILE2
      rename Rob top2
      proc
      memory
      equiv_make top1 top2 equiv
      hierarchy -top equiv
      clean -purge
      equiv_simple
      equiv_induct
      equiv_status -assert
    "
fi
