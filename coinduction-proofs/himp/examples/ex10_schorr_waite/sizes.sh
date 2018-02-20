#!/bin/sh
for f in graph.v schorr_waite.v ex2_graph.v; do
  echo -n "$f: ";
  runghc Uncomment.hs < $f | grep -v '^[[:space:]]*$' | wc -l
done
