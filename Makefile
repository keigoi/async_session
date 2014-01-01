OCAMLC=ocamlfind ocamlc -g -rectypes -thread -package async
OCAMLOPT=ocamlfind ocamlopt -g -rectypes -thread -package async
OCAMLMKTOP=ocamlfind ocamlmktop -g -rectypes -thread -package async
OCAMLDEP=ocamlfind ocamldep
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

CMI=session.cmi
BYTE_OBJS=session.cmo example.cmo
NATIVE_OBJS=$(BYTE_OBJS:%.cmo=%.cmx)

all: test.byte

test.native: $(NATIVE_OBJS) $(CMI)
	$(OCAMLOPT) -linkpkg -o test.native $(OCAMLFLAGS) $(NATIVE_OBJS)

test.byte: $(BYTE_OBJS) $(CMI)
	$(OCAMLC) -linkpkg -o test.byte $(OCAMLFLAGS) $(BYTE_OBJS)

test.top: $(BYTE_OBJS) $(CMI)
	$(OCAMLMKTOP) -linkpkg -o test.top $(OCAMLFLAGS) $(BYTE_OBJS)


# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Clean up
clean:
	rm -f test.byte test.native
	rm -f *.cm[ioaxt] *.cmax *.cmti *.o *.annot

# Dependencies
depend:
	$(OCAMLDEP) $(INCLUDES) *.mli *.ml > .depend

include .depend

