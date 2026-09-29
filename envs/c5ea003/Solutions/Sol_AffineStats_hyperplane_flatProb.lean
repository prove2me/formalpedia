-- Prove2me | solution 1 for AffineStats.hyperplane_flatProb
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:58:13.17317+00:00
-- url     : https://prove2.me/submissions/d9e7fd68-988c-44ad-b111-1b15e7a38bd1

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_card_bad
import Theorems.Thm_AffineStats_hitSet_hyp
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


lemma card_Param (n d : ℕ) : Fintype.card (Param n d) = 2 ^ (n * (d + 1)) := by
  simp [Param, ← pow_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]













variable {n d : ℕ}





variable {n d : ℕ}





variable {n d : ℕ}









variable {n d : ℕ}







































open AffineStats in
theorem solution(n d : ℕ) :
    flatProb (n + 1) (d + 1) (hyp n) (2 ^ d) = 1 - (1 / 2) ^ (d + 1) := by
  classical
  have hcards : (hitSet (n + 1) (d + 1) (hyp n) (2 ^ d)).card
      + 2 ^ (n + 1) * 2 ^ (n * (d + 1)) = 2 ^ ((n + 1) * (d + 1 + 1)) := by
    rw [hitSet_hyp, ← card_bad n d]
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Param (n + 1) (d + 1))))
      (p := fun p : Param (n + 1) (d + 1) => ∃ i, p.2 i 0 = 1)
    rw [Finset.card_univ, card_Param] at h
    convert h using 2
  have hT : (0 : ℚ) < 2 ^ ((n + 1) * (d + 1 + 1)) := by positivity
  have hQ : ((hitSet (n + 1) (d + 1) (hyp n) (2 ^ d)).card : ℚ)
      = 2 ^ ((n + 1) * (d + 1 + 1)) - 2 ^ (n + 1) * 2 ^ (n * (d + 1)) := by
    have := congrArg (fun m : ℕ => (m : ℚ)) hcards
    push_cast at this
    linarith
  rw [flatProb, hQ, sub_div]
  rw [div_self (ne_of_gt hT)]
  congr 1
  rw [div_eq_iff (ne_of_gt hT), one_div, inv_pow, inv_mul_eq_div, eq_div_iff (by positivity),
    ← pow_add, ← pow_add]
  congr 1
  ring
