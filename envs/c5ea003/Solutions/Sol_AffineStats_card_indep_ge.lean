-- Prove2me | solution 1 for AffineStats.card_indep_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:32:18.20083+00:00
-- url     : https://prove2.me/submissions/42319177-b067-4d59-8d57-72cf87dc2ae9

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_card_vanishing
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







































open AffineStats in
theorem solution(n d : ℕ) :
    2 ^ (n * (d + 1)) ≤
      (univ.filter fun v : Fin (d + 1) → Vec n => Indep v).card
        + (2 ^ (d + 1) - 1) * 2 ^ (n * d) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin (d + 1) → Vec n))) (p := fun v => Indep v)
  rw [Finset.card_univ] at hsplit
  have hcard : Fintype.card (Fin (d + 1) → Vec n) = 2 ^ (n * (d + 1)) := by
    simp [← pow_mul]
  rw [hcard] at hsplit
  have hsub : (univ.filter fun v : Fin (d + 1) → Vec n => ¬ Indep v)
      ⊆ (univ.filter fun y : Fin (d + 1) → ZMod 2 => y ≠ 0).biUnion
          (fun y => univ.filter fun v : Fin (d + 1) → Vec n => ∑ i, y i • v i = 0) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Indep, not_forall] at hv
    obtain ⟨y, hy, hy2⟩ := hv
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, hy, by simpa using hy2⟩
  have hfiber : ∀ y : Fin (d + 1) → ZMod 2, y ≠ 0 →
      (univ.filter fun v : Fin (d + 1) → Vec n => ∑ i, y i • v i = 0).card = 2 ^ (n * d) := by
    intro y hy
    have h := card_vanishing n d hy
    have h2 : 2 ^ (n * (d + 1)) = 2 ^ (n * d) * 2 ^ n := by rw [← pow_add, Nat.mul_succ]
    rw [h2] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos n) h
  have hbound : (univ.filter fun v : Fin (d + 1) → Vec n => ¬ Indep v).card
      ≤ (2 ^ (d + 1) - 1) * 2 ^ (n * d) := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    rw [Finset.sum_congr rfl (fun y hy => hfiber y (by simpa using (Finset.mem_filter.mp hy).2))]
    rw [Finset.sum_const, smul_eq_mul]
    have hnz : (univ.filter fun y : Fin (d + 1) → ZMod 2 => y ≠ 0).card = 2 ^ (d + 1) - 1 := by
      have h1 := Finset.card_filter_add_card_filter_not
        (s := (univ : Finset (Fin (d + 1) → ZMod 2))) (p := fun y => y ≠ 0)
      rw [Finset.card_univ] at h1
      have h2 : (univ.filter fun y : Fin (d + 1) → ZMod 2 => ¬ (y ≠ 0)) = {0} := by
        ext y; simp
      rw [h2] at h1
      simp only [Finset.card_singleton] at h1
      have h3 : Fintype.card (Fin (d + 1) → ZMod 2) = 2 ^ (d + 1) := by simp
      omega
    rw [hnz]
  omega
