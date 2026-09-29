-- Prove2me | solution 1 for AffineStats.key_pair_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:28.765572+00:00
-- url     : https://prove2.me/submissions/63139a14-1197-4b94-a3c0-669516bb7a61

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_card_sym_diff_pairs
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



/-- The elementary inequality `4 m (M - m) ≤ M²` behind the parity bound. -/
lemma four_mul_mul_le (M m : ℕ) (h : m ≤ M) : 4 * (m * (M - m)) ≤ M * M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Nat.add_sub_cancel_left]
  zify
  nlinarith [sq_nonneg ((m : ℤ) - k)]






variable {n d : ℕ}







































open AffineStats in
theorem solution(A : Finset (Vec n)) (w : Fin d → Vec n) :
    2 * (univ.filter fun p : Vec n × Vec n =>
          ¬ (2 ∣ (cnt A p.1 w + cnt A (p.1 + p.2) w))).card ≤ 2 ^ (2 * n) := by
  classical
  set S : Finset (Vec n) := univ.filter fun c : Vec n => ¬ (2 ∣ cnt A c w) with hS
  have hset : (univ.filter fun p : Vec n × Vec n => ¬ (2 ∣ (cnt A p.1 w + cnt A (p.1 + p.2) w)))
      = univ.filter fun p : Vec n × Vec n => ¬ ((p.1 ∈ S) ↔ (p.1 + p.2 ∈ S)) := by
    apply Finset.filter_congr
    intro p _
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hset, card_sym_diff_pairs, ← mul_assoc]
  have hle : S.card ≤ 2 ^ n := by
    rw [← card_Vec n]; exact Finset.card_le_univ S
  calc 2 * 2 * (S.card * (2 ^ n - S.card)) = 4 * (S.card * (2 ^ n - S.card)) := by ring
    _ ≤ 2 ^ n * 2 ^ n := four_mul_mul_le _ _ hle
    _ = 2 ^ (2 * n) := by rw [two_mul, pow_add]
