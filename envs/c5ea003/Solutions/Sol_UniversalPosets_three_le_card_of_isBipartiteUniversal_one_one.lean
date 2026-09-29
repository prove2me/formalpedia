-- Prove2me | solution 1 for UniversalPosets.three_le_card_of_isBipartiteUniversal_one_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:26:47.59712+00:00
-- url     : https://prove2.me/submissions/0a568297-9746-4132-9800-60170568dd3f

-- Sol generated from Cryptography/UniversalPosets/SmallCases.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_Bounds

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

/-- In a type with at most two elements, three points cannot be pairwise distinct. -/
theorem eq_of_card_le_two {U : Type*} [Fintype U] [DecidableEq U]
    (hcard : Fintype.card U ≤ 2) (x y z : U) : x = y ∨ x = z ∨ y = z := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hxy, hxz, hyz⟩ := hcon
  have h3 : ({x, y, z} : Finset U).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hle : ({x, y, z} : Finset U).card ≤ Fintype.card U := Finset.card_le_univ _
  omega






open UniversalPosets in
theorem solution{U : Type*} [PartialOrder U] [Fintype U]
    (h : IsBipartiteUniversal U 1 1) : 3 ≤ Fintype.card U := by
  classical
  by_contra hc
  push_neg at hc
  have hcard : Fintype.card U ≤ 2 := by omega
  obtain ⟨f, hf⟩ := h (fun _ _ => True)
  obtain ⟨g, hg⟩ := h (fun _ _ => False)
  set u := f (Sum.inl 0) with hu
  set v := f (Sum.inr 0) with hv
  set p := g (Sum.inl 0) with hp
  set q := g (Sum.inr 0) with hq
  have huv : u ≤ v := (hf (Sum.inl 0) (Sum.inr 0)).2 (by simp [bipRel])
  have hvu : ¬ v ≤ u := fun hh => by
    simpa [bipRel] using (hf (Sum.inr 0) (Sum.inl 0)).1 hh
  have hune : u ≠ v := fun e => hvu (le_of_eq e.symm)
  have hpq : ¬ p ≤ q := fun hh => by
    simpa [bipRel] using (hg (Sum.inl 0) (Sum.inr 0)).1 hh
  have hqp : ¬ q ≤ p := fun hh => by
    simpa [bipRel] using (hg (Sum.inr 0) (Sum.inl 0)).1 hh
  have hpne : p ≠ q := fun e => hpq (le_of_eq e)
  have hpuv : p = u ∨ p = v := by
    rcases eq_of_card_le_two hcard p u v with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hune
  have hquv : q = u ∨ q = v := by
    rcases eq_of_card_le_two hcard q u v with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hune
  rcases hpuv with hpu | hpv <;> rcases hquv with hqu | hqv
  · exact hpne (hpu.trans hqu.symm)
  · exact hpq (by rw [hpu, hqv]; exact huv)
  · exact hqp (by rw [hpv, hqu]; exact huv)
  · exact hpne (hpv.trans hqv.symm)
