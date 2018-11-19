Casper Proofs
=============

This project provides models and proofs of the [Casper](https://github.com/ethereum/casper)
blockchain finality system in Coq.
The major theorems currently proven are Accountable Safety and
Plausible Liveness.
These proofs are written to depend only loosely on the details
of an underlying blockchain, and are instantiated with models
at various levels of detail.
We also have a detailed model of the data structures and node
behavior in the Beacon Chain protocol.

A more detailed explanation of the models and proofs can be found in the
technical report:

<img src="resources/pdf-icon.png" alt="PDF" width="2%" />
*[Verification of Casper in the Coq Proof Assistant](report/report.pdf)*

Project Layout
--------------

### Casper abstract model and proofs

These files contain the major theorems about Casper.
The theorems are proven over an abstract view of block structure and
validator sets, and can be instantiated with concrete definitions
of various levels of detail without needing to modify these proofs.

- [AccountableSafety.v](Core/AccountableSafety.v): Proof of Accountable Safety, based on an Isabelle/HOL [proof](https://github.com/palmskog/pos) by Yoichi Hirai
- [PlausibleLiveness.v](Core/PlausibleLiveness.v): Proof of plausible liveness

### Validator and Blockchain models

These files give two different models meeting the abstract assumptions on validator sets:

- [ValidatorQuorum.v](Core/ValidatorQuorum.v): A simplified model defining
"2/3 weight" sets and "1/3 weight" sets by counting all validators with equal weight.
- [ValidatorDepositQuorum.v](Core/ValidatorDepositQuorum.v): A more detailed model
giving each validator a deposit and defining sets by fraction of total deposits.
Block models:

This file defines a more detailed blockchain model,
where checkpoint blocks may include a set of votes:

- [Blockforest.v](Core/Blockforest.v): definitions and utility lemmas related to block trees and blockchains

These files instantiate the Accoutable Safety theorem against some of
the models above:

- [ValidatorBlockforest.v](Core/ValidatorBlockforest.v): instantiation of all assumptions in abstract safety model for block trees
- [TransitionSystemSpec.v](Core/TransitionSystemSpec.v): simple transition system with validator-attested blocks with instantiated accountable safety

### Beacon Chain Model

- [Node.v](Core/Node.v): Coq representations of Beacon chain data structures
- [Protocol.v](Core/Protocol.v): Coq representation of Beacon chain state updates

### Utility files

- [StrongInductionLtn.v](Core/StrongInductionLtn.v): some strong induction principles on natural numbers, adapted from work by Tej Chajed
- [ssrAC.v](Core/ssrAC.v): rewriting tactics modulo associativity and commutativity, by Cyril Cohen

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
opam install coq.8.8.2 coq-mathcomp-ssreflect.1.7.0 coq-fcsl-pcm.1.0.0 coq-hammer.1.0.9+8.8.1 coq-mathcomp-finmap.1.1.0
```

Then, run `make` in the project root directory to check all definitions and proofs.

Getting Help
------------
For inquiries or to report problems, feel free to report github issues or to contact us directly.
