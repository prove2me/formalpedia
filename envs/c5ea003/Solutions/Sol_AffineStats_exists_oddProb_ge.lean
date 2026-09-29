-- Prove2me | solution 1 for AffineStats.exists_oddProb_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:46:09.083529+00:00
-- url     : https://prove2.me/submissions/4c350dae-f48f-41fc-9486-6fa6782b3d63

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_card_indepParams
import Theorems.Thm_AffineStats_card_indep_ge
import Theorems.Thm_AffineStats_exists_oddSet_ge
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
    ∃ A : Finset (Vec n),
      (1 : ℚ) / 2 - (2 ^ (d + 1) - 1) / 2 ^ (n + 1) ≤ oddProb n (d + 1) A := by
  obtain ⟨A, hA⟩ := exists_oddSet_ge n d
  refine ⟨A, ?_⟩
  set X := (oddSet n (d + 1) A).card with hX
  -- the counting inequality
  have hN : 2 ^ (n * (d + 2)) ≤ 2 * X + (2 ^ (d + 1) - 1) * 2 ^ (n * (d + 1)) := by
    have h1 := card_indep_ge n d
    have h2 := card_indepParams n d
    have h3 : 2 ^ n * 2 ^ (n * (d + 1)) ≤ 2 ^ n *
        ((univ.filter fun v : Fin (d + 1) → Vec n => Indep v).card
          + (2 ^ (d + 1) - 1) * 2 ^ (n * d)) := Nat.mul_le_mul_left _ h1
    have h4 : 2 ^ n * 2 ^ (n * (d + 1)) = 2 ^ (n * (d + 2)) := by
      rw [← pow_add]; congr 1; ring
    have h5 : 2 ^ n * ((2 : ℕ) ^ (d + 1) - 1) * 2 ^ (n * d)
        = (2 ^ (d + 1) - 1) * 2 ^ (n * (d + 1)) := by
      rw [show (2 : ℕ) ^ (n * (d + 1)) = 2 ^ (n * d) * 2 ^ n from by
        rw [← pow_add, Nat.mul_succ]]
      ring
    rw [h4] at h3
    rw [h2] at hA
    nlinarith [h3, hA, h5]
  -- convert to the probability statement
  rw [oddProb, ← hX]
  have hone : (1 : ℕ) ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  have hD : (2 : ℚ) ^ (n * (d + 1 + 1)) = 2 ^ (n * (d + 1)) * 2 ^ n := by
    rw [← pow_add]; congr 1
  have hexp : n * (d + 2) = n * (d + 1 + 1) := by ring
  have hcast : ((2 : ℚ) ^ (d + 1) - 1) * 2 ^ (n * (d + 1)) + 2 * X
      ≥ 2 ^ (n * (d + 1)) * 2 ^ n := by
    have h := (Nat.cast_le (α := ℚ)).mpr hN
    push_cast [Nat.cast_sub hone] at h
    rw [hexp, hD] at h
    linarith
  have hpos : (0 : ℚ) < 2 ^ (n * (d + 1 + 1)) := by positivity
  have hQpos : (0 : ℚ) < 2 ^ n := by positivity
  rw [le_div_iff₀ hpos, hD]
  set P := (2 : ℚ) ^ (n * (d + 1))
  set Q := (2 : ℚ) ^ n
  set K := (2 : ℚ) ^ (d + 1)
  have hQ2 : (2 : ℚ) ^ (n + 1) = Q * 2 := by rw [pow_succ]
  rw [hQ2]
  have key : (1 / 2 - (K - 1) / (Q * 2)) * (P * Q) = P * Q / 2 - (K - 1) * P / 2 := by
    field_simp
  rw [key]
  linarith
