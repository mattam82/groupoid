COQDOCOPTS=--utf8 -g --interpolate -coqlib http://coq.inria.fr/stdlib/ -R ../theories Groupoid
COQOPTS=
COQBIN=
THEORIES = ../theories

all: coq main.pdf

coq:
	cd .. && $(MAKE)

%.tex: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --body-only --latex -o $@ ${<:.vo=.v}

%.html: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --html -o $@ ${<:.vo=.v}

%.pdf: %.tex
	rubber -d $<

clean:
	cd .. && $(MAKE) clean
	rm -f ${TARGETS}

main.pdf: introduction.tex setting.tex ${THEORIES}/cwf_equations.tex ${THEORIES}/groupoid.tex ${THEORIES}/groupoid_interpretation_def.tex ${THEORIES}/groupoid_interpretation.tex ${THEORIES}/cwf_equations.tex ${THEORIES}/fun_ext.tex

pdf : ${THEORIES}/groupoid.tex ${THEORIES}/groupoid_interpretation_def.tex
	/bin/sh notations.sed
	rubber -d main
