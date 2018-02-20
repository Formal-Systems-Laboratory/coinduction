#!/bin/bash
kcoq --simple-names --no-quotes syntax himp.lk fun_domains.v
kcoq --simple-names --no-quotes rules --extra-rules fun_aux_steps.txt himp.lk fun_steps.v
