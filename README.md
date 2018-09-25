Casper Toychain
===============

[![Build Status](https://travis-ci.org/palmskog/caspertoychain.svg?branch=master)](https://travis-ci.org/palmskog/caspertoychain)

Minimalistic set of definitions and lemmas for verification of the [Casper](https://github.com/ethereum/casper) smart contract, extracted from [Toychain](https://github.com/certichain/toychain).

Requirements
------------

* [Coq 8.7 or 8.8](https://coq.inria.fr)
* [Mathematical Components 1.6.4 or 1.7.0](http://math-comp.github.io/math-comp/) (`ssreflect`)
* [FCSL PCM library 1.0.0](https://github.com/imdea-software/fcsl-pcm)
* [CoqHammer 1.0.9](https://github.com/lukaszcz/coqhammer)

Building
--------

We recommend installing dependencies via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-mathcomp-ssreflect coq-fcsl-pcm coq-hammer
```

Then, run `make` in the project root directory to check all definitions and proofs.
