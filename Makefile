
COQC = coqc
COQDOC = coqdoc
DOCFLAGS = -g -d doc/ --html --utf8

#NB: qtemp takes a while to compile, avoid making changes in preceding files

VFILES = tactics.v\
	axioms.v\
	functions.v\
	ordinals.v\
	lci.v\
	aac.v\
	ring.v\
	cardinal.v\
	ordinal_arith.v\
	nnum_base.v\
	quotient.v\
	utils1.v

#	ztemp.v\
#	qtemp.v\
#	qfrac.v\

#	raxioms.v\
#	zorn.v\
#	dedekind.v\

VOFILES = $(VFILES:.v=.vo)
GLOBFILES = $(VFILES:.v=.glob)
DOCFILES = $(patsubst %.v,doc/%.html,$(VFILES))

all: $(VOFILES) document

compile: $(VOFILES)

tactics.vo: tactics.v
	$(COQC) $<

axioms.vo: axioms.v tactics.vo
	$(COQC) $<

functions.vo: functions.v axioms.vo

ordinals.vo: ordinals.v functions.vo
	$(COQC) $<

lci.vo: lci.v ordinals.vo
	$(COQC) $<

aac.vo: aac.v lci.vo
	$(COQC) $<

ring.vo: ring.v lci.vo aac.vo
	$(COQC) $<

cardinal.vo: cardinal.v ordinals.vo
	$(COQC) $<

ordinal_arith.vo: ordinal_arith.v lci.vo cardinal.vo ring.vo
	$(COQC) $<

nnum_base.vo: nnum_base.v ordinal_arith.vo
	$(COQC) $<

quotient.vo: quotient.v nnum_base.vo
	$(COQC) $<

utils1.vo: utils1.v nnum_base.vo
	$(COQC) $<
	
%.vo %.glob: %.v
	$(COQC) $<

document: doc/index.html

doc/index.html: $(VFILES) $(GLOBFILES)
	$(COQDOC) $(DOCFLAGS) $(VFILES)

clean: 
	rm -f *.v.d *.crashcoqide

new: clean
	rm *.glob *.vo doc/*.html


