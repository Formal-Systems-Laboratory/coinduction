#!/bin/bash
echo "Testing IMP Syntax"
kcoq syntax --recursive imp.k imp_domains_test.v \
  && diff imp_domains.v imp_domains_test.v
if [ $# -eq 0 ];
  then rm -f imp_domains_test.v
fi
echo "Testing IMP Rules"
kcoq rules --recursive --lang-name imp imp.k --rules-from imp.coq imp_rules_test.v \
  && diff imp_rules.v imp_rules_test.v
if [ $# -eq 0 ];
  then rm -f imp_rules_test.v
fi
