COQDOCOPTS=--utf8 -g --interpolate -coqlib http://coq.inria.fr/stdlib/
COQOPTS=-q -R . Groupoid
TARGETS=notations.vo notations.tex defU.vo defU.tex groupoid.vo groupoid.tex groupoid_interpretation_def.vo groupoid_interpretation.vo groupoid_interpretation.tex  groupoid_interpretation_def.tex main.pdf
COQBIN=


all: ${TARGETS}

%.vo: %.v
	time ${COQBIN}coqc ${COQOPTS} $<

%.tex: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --body-only --latex -o $@ ${<:.vo=.v}

#	rm coqdoc.sty

%.html: %.vo
	${COQBIN}coqdoc ${COQOPTS} ${COQDOCOPTS} --html -o $@ ${<:.vo=.v}

%.pdf: %.tex
	rubber -d $<

clean:
	rm -f ${TARGETS}

main.pdf: introduction.tex groupoid.tex groupoid_interpretation.tex groupoid_interpretation_def.tex

groupoid_utility.vo : groupoid.vo

groupoid_utility2.vo : groupoid_interpretation_def.vo groupoid_utility.vo

groupoid_interpretation_def.vo : groupoid_utility.vo

groupoid_interpretation.vo : groupoid_utility.vo groupoid_interpretation_def.vo groupoid_utility2.vo

pdf : groupoid.tex groupoid_interpretation_def.tex
	/bin/sh notations.sed
	rubber -d main
