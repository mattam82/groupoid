COQDOCOPTS=--utf8 -g --interpolate -coqlib http://coq.inria.fr/stdlib/
COQOPTS=
TARGETS=notations.vo notations.tex defU.vo defU.tex groupoid.vo groupoid.tex  main.pdf
COQBIN=

#groupoid_interpretation.vo  groupoid_interpretation.tex	

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

main.pdf: introduction.tex setting.tex  groupoid.tex groupoid_interpretation_def_light.tex

# groupoid_interpretation.tex

groupoid.vo : HoTT_light.vo

groupoid_utility.vo : groupoid.vo

groupoid_utility2.vo : groupoid_interpretation_def.vo groupoid_utility.vo

groupoid_interpretation_def.vo : groupoid_utility.vo

# groupoid_interpretation.vo : groupoid_utility.vo groupoid_interpretation_def.vo groupoid_utility2.vo

pdf : groupoid.tex groupoid_interpretation_def_light.tex
	/bin/sh notations.sed
	rubber -d main
