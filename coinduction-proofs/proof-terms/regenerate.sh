#!/bin/bash
kcoq syntax --recursive imp.k imp_domains.v
kcoq rules --recursive --lang-name imp imp.k --rules-from imp.coq imp_rules.v
