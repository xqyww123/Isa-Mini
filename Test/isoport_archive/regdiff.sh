#!/bin/zsh
SP=/tmp/claude-1002/-home-qiyuan-Current-MLML/e23f54fc-1364-4316-a8a3-e93e30a4407e/scratchpad/isoport
norm() { sed -e "s#$SP/isamini_[a-z0-9_]*#DIR#g" \
             -e 's/(0:[0-9:]* elapsed time[^)]*)/(TIMING)/' \
             -e 's/[0-9]\+\.[0-9]\+s//g' "$1" }
for T in $@; do
  A=$SP/reg_REGBASE_$T.txt; B=$SP/reg_REGLAB2_$T.txt
  if [ ! -f $A ] || [ ! -f $B ]; then echo "$T : MISSING"; continue; fi
  if diff -q <(norm $A) <(norm $B) > /dev/null; then echo "$T : IDENTICAL"
  else echo "$T : DIFFERS"; diff <(norm $A) <(norm $B) | head -40; fi
done
