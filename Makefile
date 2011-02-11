OCAMLC=ocamlc
OCAMLCP=ocamlcp
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
INCLUDES=  # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

# prog1 should be compiled to bytecode, and is composed of three
# units: mod1, mod2 and mod3.

# The list of object files for prog1
PROG1_OBJS=simputil.cmo simp.cmo simpparser.cmo simplexer.cmo simpconsreader.cmo compactor.cmo simpgraph.cmo policylexer.ml policyparser.ml placepolicy.cmo policyparser.cmo policylexer.cmo policyreader.cmo transitiveclosure.cmo pivotlister.cmo feasible.cmo fca.cmo dominfast.cmo dominators.cmo simpdecl.cmo simpreader.cmo
PROG1_SOURCE=simputil.ml simp.ml simpparser.ml simplexer.ml simpconsreader.ml compactor.ml simpgraph.ml  placepolicy.ml policyparser.ml policylexer.ml policyreader.ml feasible.ml fca.ml transitiveclosure.ml pivotlister.ml dominators.ml dominfast.ml simpdecl.ml simpreader.ml 

main : prog1 opt

prog1: $(PROG1_OBJS)
	$(OCAMLC) -g -o simp xml-light.cma graph.cmo str.cma unix.cma $(OCAMLFLAGS) $(PROG1_OBJS)

profile: $(PROG1_OBJS)
	ocamlopt -g -o simpprofile -p xml-light.cmxa graph.cmxa str.cmxa unix.cmxa $(OCAMLFLAGS) $(PROG1_SOURCE)

opt : $(PROG1_SOURCE)
	ocamlopt -o simpopt xml-light.cmxa graph.cmxa str.cmxa unix.cmxa $(OCAMLFLAGS) $(PROG1_SOURCE)

policy : policylexer.ml policyparser.ml placepolicy.cmo policyparser.cmo policylexer.cmo policyreader.cmo
	ocamlc -o policy placepolicy.cmo policyparser.cmo policylexer.cmo policyreader.cmo

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<


simplexer.ml : simplexer.mll
	ocamllex simplexer.mll

simpparser.ml : simpparser.mly
	ocamlyacc simpparser.mly


policylexer.ml : policylexer.mll
	ocamllex policylexer.mll

policyparser.ml : policyparser.mly
	ocamlyacc policyparser.mly

# Clean up
clean:
	rm -f simp
	rm -f *.cm[iox]
	rm -f *.mli
	rm -f simpparser.ml
	rm -f simplexer.ml

# Dependencies
depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

include .depend
