(TeX-add-style-hook
 "talk2018-03-05"
 (lambda ()
   (TeX-run-style-hooks
    "latex2e"
    "article"
    "art10"
    "calc"
    "tikz-cd"
    "tensor"
    "fancyvrb"
    "todonotes"
    "verbatim"
    "amsmath"
    "microtype"
    "amssymb"
    "amsthm"
    "thmtools"
    "nameref"
    "hyperref"
    "cleveref")
   (TeX-add-symbols
    '("tens" 2)
    '("keywords" 1))
   (LaTeX-add-bibliographies
    "references"))
 :latex)

