Casper Proofs
=============

Minimalistic set of Coq definitions and lemmas for verification of the Casper blockchain finality system.

Requirements
------------

* [Coq 8.8](https://coq.inria.fr)
* [Mathematical Components 1.7.0](http://math-comp.github.io/math-comp/) (`ssreflect`)
* [FCSL PCM library 1.0.0](https://github.com/imdea-software/fcsl-pcm)
* [CoqHammer 1.0.9](https://github.com/lukaszcz/coqhammer)
* [finmap 1.1.0](https://github.com/math-comp/finmap)

Building
--------

We recommend installing dependencies via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-hammer coq-mathcomp-finmap
```

Then, run `make` in the project root directory to check all definitions and proofs.
