WARN_MSG = "(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)\n"

OTT_LOC    = ../spec

## Name of the submakefile generated by coq_makefile
COQMKFILENAME=CoqSrc.mk

LIBNAME="Top"

SYNTAX=syntax
TARGET=rules

FILES     = $(SYNTAX)_ott $(TARGET)_inf
VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)

.SECONDARY: $(VFILES)

all: coq

quick:  $(COQMKFILENAME) $(VFILES)
	@$(MAKE) -f CoqSrc.mk quick

coq: $(COQMKFILENAME) $(VFILES)
	@$(MAKE) -f CoqSrc.mk

%.vo: %.v
	@$(MAKE) -f CoqSrc.mk $*.vo


$(SYNTAX)_ott.v: $(OTT_LOC)/rules.ott
	ott -i $(OTT_LOC)/rules.ott -o $(SYNTAX)_ott.v -coq_lngen true -coq_expand_list_types true
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
	[ -z "$(DONTSTOP)" ]; then \
		echo; \
	echo "***** OTT PARSE ERROR(S) *****"; \
		grep -n '<<no parses (' $@; \
		$(RM) $@; \
		exit 1; \
	fi >&2


$(TARGET)_inf.v: $(OTT_LOC)/rules.ott
	lngen --coq $(TARGET)_inf.v --coq-ott $(SYNTAX)_ott $(OTT_LOC)/rules.ott


$(COQMKFILENAME): Makefile $(SYNTAX)_ott.v $(TARGET)_inf.v
	{ echo "-R . $(LIBNAME)" ; ls *.v ; } > _CoqProject && coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o $(COQMKFILENAME)


coqclean:
	rm -f .*.d *.conf .*.aux *.v-e *.v.d *.vo *.vok *.vos *.glob $(COQMKFILENAME)

ottclean:
	rm -f $(SYNTAX)_ott.v $(TARGET)_inf.v

clean: coqclean
