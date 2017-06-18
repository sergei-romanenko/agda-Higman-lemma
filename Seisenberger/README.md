# A constructive proof of Higman’s lemma formalized in Agda

This proof in Agda is based on

* Monika Seisenberger. 2000. **An Inductive Version of Nash-Williams'
Minimal-Bad-Sequence Argument for Higman's Lemma.**
In *Selected papers from the International Workshop on Types
for Proofs and Programs (TYPES '00)*,
Paul Callaghan, Zhaohui Luo, James McKinna, and Robert Pollack (Eds.).
Springer-Verlag, London, UK, 233-242. 

* Monika Seisenberger. 2003. **On the Constructive Content of Proofs.**
Dissertation, LMU München: Faculty of Mathematics,
Computer Science and Statistics 

This version is compatible with

* Agda 2.5.2
* The Standard Library 0.13

Note that the implementation in Agda is complete. Namely, it contains
a proof of the lemma **`good∈folder→good`**. This lemma corresponds to
Lemma 5.7i in Seisenberger's thesis (where it is just assumed to be
true "by construction"). However, writing out an accurate formalized
proof does take some effort.

The contents of files:

* `HigmanFinite.agda`. Higman's lemma for a finite alphabet.
* `HigmanFiniteExamples.agda`. Some illustrative stuff for `HigmanFinite.agda`.
* `HigmanInfinite.agda`. Higman's lemma for an infinite alphabet.

The proof in `HigmanFinite.agda` can be regarded as a simplified
version of the stuff in `HigmanInfinite.agda`. (Or, conversely,
`HigmanInfinite.agda` can be considered as an over-bloated version of
`HigmanFinite.agda`.) :-)

There exist another implementation of Seisenberger's proof for an
infinite alphabet written by William Delobel in the language of
The Coq Proof Assistant:

> <https://coq.inria.fr/V8.2pl1/contribs/HigmanS.html>

Mathematically speaking, the proof in `HigmanInfinite.agda` and
the proof by Delobel are the same. However, at the implementation
level, there are a some differences. Namely, the Agda version
differs in the following.

* The decidability of the equality of letters is neither exploited
  nor required.
* Natural numbers are not used.
* The decidability of the equality of trees  is neither required
  nor implemented.
* The order relation on trees (as defined by Seisenberger and
  Delobel) is neither used nor defined.
* Instead of the notion "a tree `t'` is a subtree of `t`" is used
  the notion "a node root `r` appears in `t`".
* Two lemmas related to tree invariants are proved directly. In
  the Coq version there is a generic theorem, which is instantiated
  to produce two specific lemmas. But, the size of two concrete
  proofs is less than that of the generic theorem. :-)
* A number of lemmas related to the equality of trees and to the
  non-emptiness of some lists in node roots are neither required
  nor proven.
* The notions of "well-foundedness" and "accessibility" are not
  used. The Agda version deals with inductive bars directly (as
  is done in Seisenberger's thesis).
* The datatype `Maybe` (corresponding to the Coq `option`)
  is not used, because all functions in the Agda version are just
  total. (In other words, when they are called, it is known
  in advance, that the expected result does exist.)

An interesting technical of the Agda version is that it makes use of
the idea of *proofs as data*, as explained in

* Nils Anders Danielsson. 2012. **Bag Equivalence via a Proof-Relevant
  Membership Relation.** LNCS Volume 7406, pp 149-165.    
  <http://dx.doi.org/10.1007/978-3-642-32347-8_11>    
  <http://www.cse.chalmers.se/~nad/publications/danielsson-bag-equivalence.html>

Constructively, if we have a proof telling that something appears in
a container, this proof explains how to actually get this thing.

