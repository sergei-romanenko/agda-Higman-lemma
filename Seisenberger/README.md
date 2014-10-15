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

* Agda 2.4.2
* The Standard Library 0.8.1

Note that the formalization in Agda is complete. Namely, it contains
a proof of the lemma **`good∈folder→good`**. This lemma corresponds to
Lemma 5.7i in Seisenberger's thesis (where it is just assumed to be
true "by construction"). However, writing out an accurate formalized
proof does take some effort.
