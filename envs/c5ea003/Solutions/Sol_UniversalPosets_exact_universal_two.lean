-- Prove2me | solution 1 for UniversalPosets.exact_universal_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:28:39.622456+00:00
-- url     : https://prove2.me/submissions/cee226f9-0556-47ae-95ec-5b67039d243e

-- Sol generated from Cryptography/UniversalPosets/SmallCases.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds
import Theorems.Thm_UniversalPosets_IsUniversalHost_congr
import Theorems.Thm_UniversalPosets_bipHost_one_one_isUniversalHost
import Theorems.Thm_UniversalPosets_card_bipHost_one_one
import Theorems.Thm_UniversalPosets_isBipartiteUniversal_of_isUniversalHost
import Theorems.Thm_UniversalPosets_three_le_card_of_isBipartiteUniversal_one_one

/-!
# Exact small cases: the counting bound is not tight

`Bounds.lean` proves `2 ^ m ≤ N ^ 2` for every host of the `(m,m)`-bipartite
posets and exhibits a host of size `m·2^m + m`.  Here the smallest case
`m = 1` (that is, `n = 2` points) is settled *exactly*: the optimal host has
`3` points, while the counting bound only gives `2`.  So the counting lower
bound is already lossy at `n = 2`, which is the finite shadow of the
`n/4` versus `n/2` gap discussed in the motivating paper.

-- !-- Lab Notes -- !--
Experiment (Experimenter).  All `19` partial orders on `3` points and all `3`
partial orders on `2` points were enumerated (see `ComputationalEvidence.md`).
For `n = 2` the three orders are the antichain and the two chains; a host must
contain a comparable pair and an incomparable pair, and a two-element poset is
either a chain or an antichain -- never both.  Hence `N ≥ 3`, and the explicit
host `BipHost 1 1` (a two-chain plus an isolated point) attains it.

Analysis (Analyst).  The obstruction is *reuse*: the counting argument allows a
host of `N` points to serve `N^n` embeddings, but comparability constraints
between host points cannot be switched off.  This is exactly the loss that the
regularity method of the paper repairs asymptotically.

Critique (Critic).  The lower bound `3 ≤ N` is proved for arbitrary finite
partially ordered hosts, not just for the constructed one, and the matching
construction is explicit; the statement is therefore sharp and non-vacuous.
-/

open UniversalPosets







open UniversalPosets in
theorem solution:
    IsUniversalHost (BipHost 1 1) (Fin 2) ∧ Fintype.card (BipHost 1 1) = 3 ∧
      ∀ (U : Type) [PartialOrder U] [Fintype U], IsUniversalHost U (Fin 2) →
        3 ≤ Fintype.card U := by
  refine ⟨bipHost_one_one_isUniversalHost, card_bipHost_one_one, fun U _ _ h => ?_⟩
  exact three_le_card_of_isBipartiteUniversal_one_one
    (isBipartiteUniversal_of_isUniversalHost (h.congr finSumFinEquiv))
