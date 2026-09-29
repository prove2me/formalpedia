-- Prove2me | Theorems.Thm_mme_stothers_general_hash_incidence_sums
-- name    : mme_stothers_general_hash_incidence_sums
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T17:14:45.038928+00:00
-- url     : https://prove2.me/theorems/dbf4874b-cf3a-4597-844d-1abd25ec716f
-- title:
--   Averaging identities for the outer hash
-- statement:
--   **Averaging identities for the outer affine hash, at any profile.**
--
--   Fix an integral ten-class profile $\beta$, a scale $m\ge1$, a prime modulus $p\ge9$ that is odd, and
--   a residue set $S$ below $p/2$. Summing over all $p^{N+2}$ affine hash states, where $N = 3Dm$ is the
--   address length:
--
--   $$\sum_{q}\bigl|\text{targets retained at }q\bigr| \;=\; |T|\,|S|\,p^{N},
--   \qquad
--   \sum_{q}\bigl|\text{target--ambient collisions retained at }q\bigr| \;\le\; |C|\,p^{N},$$
--
--   where $T$ is the set of all exact-profile addresses and $C$ the set of all ordered
--   target--ambient pairs sharing a mode word.
--
--   The first is an exact double count: a single marginal-supported address is retained at exactly
--   $|S|p^{N}$ states, because once the common hash value $s\in S$ and the free weights are chosen, the
--   affine offset is determined -- this uses that the address contains the grade $1$ somewhere in each
--   mode word, which is where positivity of the ten class counts enters. The second is an inequality
--   because a colliding pair is retained at most at $p^{N}$ states: sharing one mode word forces the two
--   addresses to differ in another, and a nonzero coordinate difference cuts the parameter space by a
--   factor $p$.
--
--   Together they are the counting input to the averaging argument: some state must retain at least the
--   average number of targets while retaining at most a controlled number of collisions.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, proof of Lemma 3.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_affine_hash

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_general_hash_incidence_sums
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r) (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp9 : 9 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2)) :
    (∑ q ∈ MME.StothersFourth.genHashStateUniverse base m p,
        (MME.StothersFourth.genExactTargetEdges (MME.StothersFourth.genHashEdgesAtState base m p S q)).card) =
        (MME.StothersFourth.genHashAllTargetEdges base m).card * S.card *
          p ^ MME.StothersFourth.genOuterLength base m ∧
      (∑ q ∈ MME.StothersFourth.genHashStateUniverse base m p,
        (MME.StothersFourth.genTargetAmbientCollisions
          (MME.StothersFourth.genHashEdgesAtState base m p S q)).card) ≤
        (MME.StothersFourth.genHashAllTargetAmbientCollisions base m).card *
          p ^ MME.StothersFourth.genOuterLength base m := by
  sorry
