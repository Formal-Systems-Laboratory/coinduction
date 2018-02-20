BASE_FILES:=maps.v sets.v proof.v proof_automation.v equate_map_reflection.v map_zipper.v
GENERATED_FILES:=imp_domains.v imp_rules.v
MANUAL_FILES:=imp_domains_aux.v imp_demo.v
FILES:=$(BASE_FILES) $(GENERATED_FILES) $(MANUAL_FILES)

include coq_makefile.mk

coq_makefile.mk : Makefile
	coq_makefile -o $@ -I . $(FILES)

.PHONY : distclean
distclean : clean
	rm -f coq_makefile.mk
