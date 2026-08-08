#!/bin/zsh
SP=/tmp/claude-1002/-home-qiyuan-Current-MLML/e23f54fc-1364-4316-a8a3-e93e30a4407e/scratchpad/isoport
TA=$1; TB=$2; shift 2
norm() { awk -v T="$2" 'index($0, T".thy") {on=1} on' "$1" \
  | sed -e "s#$SP/isamini_[a-z0-9_]*#DIR#g" \
        -e 's/(0:[0-9:]* elapsed time[^)]*)/(TIMING)/' }
for T in $@; do
  A=$SP/reg_${TA}_$T.txt; B=$SP/reg_${TB}_$T.txt
  if [ ! -f $A ] || [ ! -f $B ]; then echo "$T : MISSING"; continue; fi
  if diff -q <(norm $A $T) <(norm $B $T) > /dev/null; then echo "$T : IDENTICAL"
  else echo "$T : DIFFERS"; diff <(norm $A $T) <(norm $B $T) | head -30; fi
done
