Casper Toychain
===============

Minimalistic set of definitions for a blockchain protocol,
extracted from [Toychain](https://github.com/certichain/toychain).

Requirements
------------

* Coq 8.7 (available from https://coq.inria.fr/coq-87);
* Mathematical Components 1.6.4 (http://math-comp.github.io/math-comp/)

Building
--------

We recommend installing dependencies via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-mathcomp-ssreflect
```

Then, run `make` in the project root directory.
