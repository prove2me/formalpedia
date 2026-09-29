-- Prove2me | solution 1 for UniversalPosets.bipHost_one_one_isUniversalHost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:22:07.918703+00:00
-- url     : https://prove2.me/submissions/336e1586-4158-416f-b9a5-7ec58dde4792

-- Sol generated from Cryptography/UniversalPosets/SmallCases.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds
import Theorems.Thm_UniversalPosets_bipHost_le_def

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
theorem solution: IsUniversalHost (BipHost 1 1) (Fin 2) := by
  classical
  intro r hr
  by_cases h01 : r 0 1
  · have h10 : ¬ r 1 0 := fun hh => by
      have : (0 : Fin 2) = 1 := antisymm_of r h01 hh
      exact absurd this (by decide)
    refine ⟨![(Sum.inl 0 : BipHost 1 1), (Sum.inr (Set.univ, 0) : BipHost 1 1)], ?_⟩
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [bipHostLe, h01, h10, refl_of r]
  · by_cases h10 : r 1 0
    · refine ⟨![(Sum.inr (Set.univ, 0) : BipHost 1 1), (Sum.inl 0 : BipHost 1 1)], ?_⟩
      intro x y
      fin_cases x <;> fin_cases y <;>
        simp [bipHostLe, h01, h10, refl_of r]
    · refine ⟨![(Sum.inl 0 : BipHost 1 1), (Sum.inr (∅, 0) : BipHost 1 1)], ?_⟩
      intro x y
      fin_cases x <;> fin_cases y <;>
        simp [bipHostLe, h01, h10, refl_of r]
