(TeX-add-style-hook "setting"
 (lambda ()
    (LaTeX-add-labels
     "sec:setting-translation"
     "sec:proof-assistant"
     "sec:polym-univ")
    (TeX-add-symbols
     "Types")
    (TeX-run-style-hooks
     "corett")))

