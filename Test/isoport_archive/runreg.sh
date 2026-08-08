#!/bin/zsh
SP=/tmp/claude-1002/-home-qiyuan-Current-MLML/e23f54fc-1364-4316-a8a3-e93e30a4407e/scratchpad/isoport
cd /home/qiyuan/Current/MLML
DIR=$1; TAG=$2; shift 2
for T in "$@"; do
  ./contrib/Isabelle2025-2/bin/isabelle process_theories -d contrib -l Auto_Sledgehammer -O -U -m 200 -D $SP/$DIR $T > $SP/reg_${TAG}_$T.txt 2>&1
  echo "===== $TAG / $T : exit=$?"
done
