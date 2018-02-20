FILES:=CSLSets.v Map.v ConcurrentSeparationLogic.v ConcurrentSeparationLogic2.v

include coq_makefile.mk

coq_makefile.mk : Makefile
	coq_makefile -I ../common/ $(FILES) > $@
