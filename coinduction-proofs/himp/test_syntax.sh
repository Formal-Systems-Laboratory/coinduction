#!/bin/bash
echo "Testing HIMP Syntax"
kcoq --simple-names --no-quotes syntax himp.lk fun_domains_test.v \
 && diff fun_domains.v fun_domains_test.v
rm -f fun_domains_test.v
