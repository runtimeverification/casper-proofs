Casper Proofs
=============

Coq definitions and proofs for verification of the Casper blockchain finality system.

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


Files
------

Utility files:

- [StrongInductionLtn.v](Core/StrongInductionLtn.v): some strong induction principles on natural numbers, adapted from work by Tej Chajed
- [ssrAC.v](Core/ssrAC.v): rewriting tactics modulo associativity and commutativity, by Cyril Cohen

Casper-related files:

- [CasperOneMessage.v](Core/CasperOneMessage.v): abstract model of Casper, including proof of accountable safety, based on Isabelle/HOL proof by Hirai
- [PlausibleLiveness.v](Core/PlausibleLiveness.v): abstract model of Casper, including proof of plausible liveness
- [ValidatorQuorum.v](Core/ValidatorQuorum.v): instantiation of quorum (honest node) assumptions using _validator set cardinality_ in the abstract model for safety
- [ValidatorDepositQuorum.v](Core/ValidatorDepositQuorum.v): instantiation of quorum (honest node) assumptions using _sums of validator set deposits_ in the abstract model for safety
- [Blockforest.v](Core/Blockforest.v): definitions and utility lemmas related to block trees and blockchains
- [ValidatorBlockforest.v](Core/ValidatorBlockforest.v): instantiation of all assumptions in abstract safety model for block trees
- [ValidatorBlockforest.v](Core/ValidatorBlockforest.v): instantiation of all assumptions in abstract safety model for block trees
- [TransitionSystemSpec.v](Core/TransitionSystemSpec.v): simple transition system with validator-attested blocks with instantiated accountable safety
- [Node.v](Core/Node.v): Coq model of Beacon chain data structures
- [Protocol.v](Core/Protocol.v): Coq model of Beacon chain state updates

