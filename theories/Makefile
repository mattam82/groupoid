COQDOCOPTS=--utf8 -g --interpolate -coqlib http://coq.inria.fr/stdlib/
COQOPTS=
TARGETS=${THEORIES}/notations.tex ${THEORIES}/defU.tex ${THEORIES}/groupoid.tex main.pdf
COQBIN=
THEORIES = .

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

main.pdf: ${THEORIES}/groupoid.tex ${THEORIES}/groupoid_interpretation_def.tex ${THEORIES}/groupoid_interpretation.tex ${THEORIES}/fun_ext.tex

# groupoid_interpretation.tex

groupoid.vo : ${THEORIES}/HoTT_light.vo

groupoid_utility.vo : ${THEORIES}/groupoid.vo

groupoid_utility2.vo : ${THEORIES}/groupoid_interpretation_def.vo ${THEORIES}/groupoid_interpretation.tex ${THEORIES}/groupoid_utility.vo

groupoid_interpretation_def.vo : ${THEORIES}/groupoid_utility.vo

# groupoid_interpretation.vo : groupoid_utility.vo groupoid_interpretation_def.vo groupoid_utility2.vo

pdf : ${THEORIES}/groupoid.tex ${THEORIES}/groupoid_interpretation_def.tex
	/bin/sh notations.sed
	rubber -d main
