FILES:=fun_domains.v fun_domains_props.v fun_domains_sugar.v fun_steps.v fun_semantics.v

include coq_makefile.mk

coq_makefile.mk : Makefile
	coq_makefile -I ../common/ $(FILES) > $@
