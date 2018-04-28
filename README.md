# Postulated Colimits in Coq

 A development of the theory of postulated colimits in Coq. Includes a proof that the pushout of a monomorphism is a monomorphism in a 'sheaf topos'.

## Prerequisites

Install Coq [here](https://coq.inria.fr/).

If developing in emacs place the following lines:

```
(setq coq-load-path-include-current t)
(setq coq-compile-before-require t)
```

in your init file.
If not then you may have to run coqc on the various dependencies to run the proofs.

## Acknowledgements

* [Coq](https://coq.inria.fr/) - Proof Assistant
* Postulated colimits and left exactness of Kan-extensions, Anders Kock[here](http://home.math.au.dk/kock/postulated.pdf)
