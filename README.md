# Postulated Colimits in Coq

 A development of the theory of postulated colimits in Coq. Includes a proof that the pushout of a monomorphism is a monomorphism in a 'sheaf topos'.

## Getting Started

These instructions will get you a copy of the project up and running on your local machine for development and testing purposes. See deployment for notes on how to deploy the project on a live system.

### Prerequisites

Install Coq [here](https://coq.inria.fr/).

If developing in emacs place the following lines:

```
(setq coq-load-path-include-current t)
(setq coq-compile-before-require t)
```

in your init file.
If not then you may have to run coqc on the various dependcies to run the proofs.

## Built With

* [Coq](https://coq.inria.fr/) - Proof Assistant
