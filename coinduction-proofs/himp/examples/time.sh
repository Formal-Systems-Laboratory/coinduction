#!/bin/sh
OPTS="-I ../../../common -I ../.."
for f in ex*.v; do
  echo $f coqc;
  time coqc $OPTS "$f" 2>&1 \
    | sed 's/.*system //;s/elapsed.*//;t;d';
  echo $f coqchk;
  time coqchk -silent $OPTS -norec $(basename "$f" .v) 2>&1 \
    | sed 's/.*system //;s/elapsed.*//;t;d';
done
