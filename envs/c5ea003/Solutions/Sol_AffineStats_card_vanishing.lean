-- Prove2me | solution 1 for AffineStats.card_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:30:28.625036+00:00
-- url     : https://prove2.me/submissions/9ac201c1-5a0c-4d1f-85ea-9b4e889ae8f5

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_sum_smul_update
import Theorems.Thm_AffineStats_vadd_self
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Affine subspace statistics in `𝔽₂ⁿ` : parity bounds

Motivated by the *affine subspace statistics problem* (the maximum, over `A ⊆ 𝔽₂ⁿ`, of
`P[|F ∩ A| = s]` for a uniformly random `d`-flat `F`), this file develops a fully finite,
self-contained model of the problem and proves sharp bounds for the *parity* statistic.

## The model

Instead of sampling a `d`-flat directly we sample an affine map `𝔽₂^d → 𝔽₂ⁿ`: a base point
`c` and direction vectors `v₀, …, v_{d-1}`, all uniform and independent. The associated
"affine `d`-cube" is the multiset `{c + ∑ yᵢ vᵢ : y ∈ 𝔽₂^d}` and
`cnt A c v = #{y : c + ∑ yᵢ vᵢ ∈ A}` is the number of its points (with multiplicity) in `A`.
When `v₀, …, v_{d-1}` are linearly independent — which happens with probability
`1 - O(2^{d-n})` — the cube is exactly a `d`-flat and `cnt A c v = |F ∩ A|`. Hence all
`n → ∞` limits of the two models agree, and this model is the convenient one for finite
combinatorial arguments.

## Main results

* `AffineStats.sum_cnt` : the first moment, `E[cnt] = 2^d · |A| / 2ⁿ`.
* `AffineStats.flatProb_compl` : the duality `λ(d, s) = λ(d, 2^d - s)` obtained by
  complementing `A`.
* `AffineStats.oddProb_le_half` : **the parity bound.** For every `n`, every `d ≥ 1` and
  every `A ⊆ 𝔽₂ⁿ`, the probability that a random affine `d`-cube meets `A` in an odd
  number of points is at most `1/2`.
* `AffineStats.flatProb_le_half_of_odd` : consequently `λ(d, s) ≤ 1/2` for every *odd* `s`.
* `AffineStats.exists_oddProb_ge` : the bound `1/2` is asymptotically attained; averaging
  over all `A` produces a set with odd-intersection probability `≥ 1/2 - (2^d-1)/2^{n+1}`.
* `AffineStats.tendsto_maxOddProb` : hence `maxₐ P[|F ∩ A| odd] → 1/2` as `n → ∞`.
* `AffineStats.hyperplane_flatProb` : for the hyperplane `A = {x : x₀ = 0}` one has
  `P[|F ∩ A| = 2^{d-1}] = 1 - 2^{-d}` *exactly*; this is the `k = d-1` case of the
  standard lower-bound construction `λ*(d, j·2^k) ≥ 1 - 2^{-k}`.
* `AffineStats.exists_flatProb_gt_half` : the parity bound does **not** extend to even `s`.
* `AffineStats.tendsto_maxFlatProb_one` : `λ*(1, 1) = 1/2`, the `d = 1` instance of the
  exact determination of `λ*(d, 1)`.
* `AffineStats.flatProb_univ` : at `s = 2^d` the value is `1`, so the regime `s < 2^d` is
  essential in the formula `λ*(d, j·2^k) = 1 - 2^{-k}`.
* `AffineStats.maxOddProb_dim2_lt_half` : at `n = d = 2` the bound `1/2` is not attained,
  so `1/2` is a genuine limit rather than a finite-`n` maximum.
-/

open AffineStats

open Finset










variable {n d : ℕ}















variable {n d : ℕ}





variable {n d : ℕ}





variable {n d : ℕ}









variable {n d : ℕ}




/-- A nonzero vector of `𝔽₂^k` has a coordinate equal to `1`. -/
lemma exists_coord_one {k : ℕ} {y : Fin k → ZMod 2} (hy : y ≠ 0) : ∃ i, y i = 1 := by
  by_contra h
  push_neg at h
  apply hy
  funext i
  have h2 := h i
  simp only [Pi.zero_apply]
  revert h2
  generalize y i = t
  revert t
  decide



































open AffineStats in
theorem solution(n d : ℕ) {y : Fin (d + 1) → ZMod 2} (hy : y ≠ 0) :
    (univ.filter fun v : Fin (d + 1) → Vec n => ∑ i, y i • v i = 0).card * 2 ^ n
      = 2 ^ (n * (d + 1)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_coord_one hy
  set F : Finset (Fin (d + 1) → Vec n) := univ.filter fun v => ∑ i, y i • v i = 0 with hF
  have hbij : (F ×ˢ (univ : Finset (Vec n))).card
      = (univ : Finset (Fin (d + 1) → Vec n)).card := by
    refine Finset.card_nbij' (fun q => Function.update q.1 i₀ (q.1 i₀ + q.2))
      (fun w => (Function.update w i₀ (w i₀ + ∑ i, y i • w i), ∑ i, y i • w i)) ?_ ?_ ?_ ?_
    · intro q hq; simp
    · intro w hw
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and, hF]
      refine ⟨?_, trivial⟩
      rw [sum_smul_update y w i₀ hi₀]
      rw [show (w i₀ + ∑ i, y i • w i + w i₀) = (∑ i, y i • w i) + (w i₀ + w i₀) from by abel,
        vadd_self, add_zero]
      exact vadd_self _
    · intro q hq
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and, hF] at hq
      obtain ⟨hq1, -⟩ := hq
      dsimp only
      have hs : ∑ i, y i • Function.update q.1 i₀ (q.1 i₀ + q.2) i = q.2 := by
        rw [sum_smul_update y q.1 i₀ hi₀, hq1]
        rw [show (0 + (q.1 i₀ + q.2 + q.1 i₀)) = q.2 + (q.1 i₀ + q.1 i₀) from by abel,
          vadd_self, add_zero]
      rw [hs, Function.update_idem, Function.update_self]
      rw [show (q.1 i₀ + q.2 + q.2) = q.1 i₀ + (q.2 + q.2) from by abel, vadd_self, add_zero]
      rw [Function.update_eq_self]
    · intro w hw
      dsimp only
      rw [Function.update_idem, Function.update_self]
      rw [show (w i₀ + (∑ i, y i • w i) + ∑ i, y i • w i)
          = w i₀ + ((∑ i, y i • w i) + (∑ i, y i • w i)) from by abel, vadd_self, add_zero]
      exact Function.update_eq_self i₀ w
  rw [Finset.card_product] at hbij
  simp only [Finset.card_univ, card_Vec] at hbij
  rw [hbij]
  simp [← pow_mul]
