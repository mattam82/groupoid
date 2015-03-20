(TeX-add-style-hook "main"
 (lambda ()
    (LaTeX-add-bibliographies
     "biblio")
    (LaTeX-add-labels
     "sec:formalization"
     "sec:interpretation")
    (TeX-add-symbols
     '("ms" 1)
     '("nt" 1)
     '("mynote" 2)
     '("aidememoire" 1)
     "mathbb"
     "coqdockwcolor"
     "interp"
     "textchi"
     "textbeta"
     "coqlibrary"
     "coqcode"
     "kw"
     "coqdoccst"
     "cst"
     "eqty"
     "matcheqkw"
     "matcheq"
     "vec"
     "nfdelta"
     "nfdeltab"
     "hnfbetadelta"
     "lrule"
     "mathrm")
    (TeX-run-style-hooks
     "url"
     "coqdoc"
     "color"
     "qsymbols"
     "code"
     "coq"
     "abbrevs"
     "hyperref"
     "xspace"
     "tikz"
     "xcolor"
     "bbold"
     "stmaryrd"
     "amscd"
     "aeguill"
     "ae"
     "amsmath"
     "amssymb"
     "latexsym"
     "subfig"
     "stfloats"
     "float"
     "utf"
     "fontenc"
     "T1"
     "latex2e"
     "llncs10"
     "llncs"
     "runningheads"
     "a4paper"
     "univmacros"
     "introduction"
     "setting"
     "../theories/groupoid"
     "../theories/groupoid_interpretation_def"
     "../theories/groupoid_interpretation"
     "../theories/fun_ext"
     "../theories/cwf_equations"
     "related-concl")))

