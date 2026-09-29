-- Prove2me | solution 1 for AffineStats.card_exactly_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:28:11.730062+00:00
-- url     : https://prove2.me/submissions/2b640b13-ed12-4641-a4b7-d0c6a9e45a02

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_card_zero_at_singleton
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the random construction for `s = 1`

This file continues the development of
`Catalog/Applications/AffineSubspaceStats/AffineStats.lean`, where the model
(random affine `d`-cubes in `𝔽₂ⁿ`, the statistic `cnt`, the probability `flatProb`)
is set up.

The paper's `s = 1` regime is governed by a *random* construction: keep each point of
`𝔽₂ⁿ` independently with probability `p`.  A `d`-flat `F` has `2^d` points, so it meets
such a random set in exactly one point with probability `2^d · p · (1-p)^{2^d - 1}`,
which is maximised at `p = 2^{-d}`, giving `(1 - 2^{-d})^{2^d - 1} → e^{-1}`.

We formalise this as a *counting* argument (no measure theory): instead of a random
subset we average over the `(m+1)^{2ⁿ}` colourings `g : 𝔽₂ⁿ → Fin (m+1)` and take
`A = g⁻¹(0)`, which realises `p = 1/(m+1)` exactly.  The combinatorial heart is
`AffineStats.card_exactly_one`: for a fixed set `T` of `t` points, exactly
`t · m^{t-1} · (m+1)^{|α| - t}` colourings vanish at exactly one point of `T`.

The main results are

* `AffineStats.exists_flatProb_one_ge` :
  `∃ A, λ(d+1,1) ≥ (2^{d+1}·m^{2^{d+1}-1} / (m+1)^{2^{d+1}}) · (1 - (2^{d+1}-1)/2ⁿ)`
  for every `m`;
* `AffineStats.exists_flatProb_one_ge_opt` : the choice `m + 1 = 2^{d+1}`, giving
  `λ(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1} · (1 - (2^{d+1}-1)/2ⁿ)`;
* `AffineStats.maxFlatProb_one_ge_limit` : hence
  `λ*(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1}`, which for `d = 0` is the exact value `1/2`
  and for every `d` beats the algebraic construction of
  `Catalog/Applications/AffineSubspaceStats/ExactProduct.lean` (e.g. `27/64` versus
  `3/8` for `2`-flats).
-/

open AffineStats

open Finset


variable {α : Type*} [Fintype α] [DecidableEq α]






variable {n d : ℕ}





















open Filter





open AffineStats in
theorem solution(T : Finset α) (m : ℕ) :
    (univ.filter fun g : α → Fin (m + 1) => (T.filter fun x => g x = 0).card = 1).card
      = T.card * (m ^ (T.card - 1) * (m + 1) ^ (Fintype.card α - T.card)) := by
  classical
  have hbi : (univ.filter fun g : α → Fin (m + 1) => (T.filter fun x => g x = 0).card = 1)
      = T.biUnion (fun x₀ => univ.filter fun g : α → Fin (m + 1) =>
          T.filter (fun x => g x = 0) = {x₀}) := by
    ext g
    simp only [mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
      refine ⟨a, ?_, ha⟩
      have hmem : a ∈ T.filter (fun x => g x = 0) := by rw [ha]; simp
      exact (mem_filter.mp hmem).1
    · rintro ⟨a, _, ha⟩
      rw [ha]; simp
  rw [hbi, Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun x₀ hx₀ => card_zero_at_singleton T m hx₀),
      Finset.sum_const, smul_eq_mul]
  · intro a _ b _ hab
    simp only [Finset.disjoint_left, mem_filter, mem_univ, true_and]
    rintro g h1 h2
    rw [h1] at h2
    exact hab (by simpa using h2)
