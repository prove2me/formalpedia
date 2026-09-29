-- Prove2me | solution 1 for AffineStats.card_zero_at_singleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:26:45.933964+00:00
-- url     : https://prove2.me/submissions/086c63ee-bdd3-4d08-b3a1-aca85d3265da

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_prod_local_values
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
theorem solution(T : Finset α) (m : ℕ) {x₀ : α} (hx₀ : x₀ ∈ T) :
    (univ.filter fun g : α → Fin (m + 1) => T.filter (fun x => g x = 0) = {x₀}).card
      = m ^ (T.card - 1) * (m + 1) ^ (Fintype.card α - T.card) := by
  classical
  set f : α → Fin (m + 1) → ℕ := fun x a =>
    if x = x₀ then (if a = 0 then 1 else 0) else if x ∈ T then (if a = 0 then 0 else 1) else 1
    with hf
  -- the defining condition is a product of local indicators
  have hind : ∀ g : α → Fin (m + 1),
      (if T.filter (fun x => g x = 0) = {x₀} then 1 else 0) = ∏ x, f x (g x) := by
    intro g
    have hiff : T.filter (fun x => g x = 0) = {x₀} ↔
        (g x₀ = 0 ∧ ∀ x ∈ T, x ≠ x₀ → g x ≠ 0) := by
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · have hmem : x₀ ∈ T.filter (fun x => g x = 0) := by rw [h]; simp
          exact (mem_filter.mp hmem).2
        · intro x hx hne hg
          have hmem : x ∈ T.filter (fun x => g x = 0) := mem_filter.mpr ⟨hx, hg⟩
          rw [h, mem_singleton] at hmem
          exact hne hmem
      · rintro ⟨h1, h2⟩
        ext x
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hx, hgx⟩
          by_contra hne
          exact h2 x hx hne hgx
        · rintro rfl; exact ⟨hx₀, h1⟩
    by_cases hP : T.filter (fun x => g x = 0) = {x₀}
    · rw [if_pos hP]
      rw [hiff] at hP
      symm
      refine Finset.prod_eq_one (fun x _ => ?_)
      by_cases hx : x = x₀
      · subst hx; simp [hf, hP.1]
      · by_cases hxT : x ∈ T
        · simp [hf, hx, hxT, hP.2 x hxT hx]
        · simp [hf, hx, hxT]
    · rw [if_neg hP]
      rw [hiff] at hP
      push_neg at hP
      symm
      by_cases h1 : g x₀ = 0
      · obtain ⟨x, hxT, hne, hgx⟩ := hP h1
        exact Finset.prod_eq_zero (mem_univ x) (by simp [hf, hne, hxT, hgx])
      · exact Finset.prod_eq_zero (mem_univ x₀) (by simp [hf, h1])
  have hsum : (univ.filter fun g : α → Fin (m + 1) => T.filter (fun x => g x = 0) = {x₀}).card
      = ∑ g : α → Fin (m + 1), ∏ x, f x (g x) := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl (fun g _ => hind g)
  have hswap := Finset.prod_univ_sum (ι := α) (R := ℕ) (κ := fun _ => Fin (m + 1))
    (fun _ => (univ : Finset (Fin (m + 1)))) f
  rw [Fintype.piFinset_univ] at hswap
  rw [hsum, ← hswap]
  -- evaluate the local sums
  refine prod_local_values T m hx₀ _ (fun x => ?_)
  by_cases hx : x = x₀
  · simp [hf, hx]
  · by_cases hxT : x ∈ T
    · simp only [hf, if_neg hx, if_pos hxT]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
      simp [Finset.filter_ne']
    · simp [hf, hx, hxT]
