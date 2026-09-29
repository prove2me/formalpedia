-- Prove2me | solution 1 for AffineStats.tendsto_maxOddProb
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:58:15.402761+00:00
-- url     : https://prove2.me/submissions/6bd43d0d-af3f-42f3-8d3f-ba59962c8445

-- Sol generated from Applications/AffineSubspaceStats/AffineStats.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Theorems.Thm_AffineStats_exists_oddProb_ge
import Theorems.Thm_AffineStats_oddProb_le_half
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














lemma maxOddProb_le_half (n d : ℕ) : maxOddProb n (d + 1) ≤ 1 / 2 := by
  apply Finset.sup'_le
  intro A _
  exact oddProb_le_half n d A

lemma maxOddProb_ge (n d : ℕ) :
    (1 : ℚ) / 2 - (2 ^ (d + 1) - 1) / 2 ^ (n + 1) ≤ maxOddProb n (d + 1) := by
  obtain ⟨A, hA⟩ := exists_oddProb_ge n d
  exact le_trans hA (Finset.le_sup' (fun A => oddProb n (d + 1) A) (mem_univ A))
























open AffineStats in
theorem solution(d : ℕ) :
    Filter.Tendsto (fun n => ((maxOddProb n (d + 1) : ℚ) : ℝ)) Filter.atTop
      (nhds (1 / 2 : ℝ)) := by
  have hlow : Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / 2 - (2 ^ (d + 1) - 1) / 2 ^ (n + 1)) Filter.atTop
      (nhds (1 / 2 : ℝ)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ (n + 1))
        Filter.atTop (nhds 0) := by
      have hgeom : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hrw : (fun n : ℕ => ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ (n + 1))
          = fun n : ℕ => (((2 : ℝ) ^ (d + 1) - 1) / 2) * ((1 / 2) ^ n) := by
        funext n
        rw [div_pow, one_pow, pow_succ]
        field_simp
        ring
      rw [hrw]
      simpa using hgeom.const_mul (((2 : ℝ) ^ (d + 1) - 1) / 2)
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / 2) (f := Filter.atTop (α := ℕ))).sub h0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds ?_ ?_
  · intro n
    have h1 : ((1 : ℚ) / 2 - (2 ^ (d + 1) - 1) / 2 ^ (n + 1) : ℚ)
        ≤ (maxOddProb n (d + 1) : ℚ) := maxOddProb_ge n d
    have h2 := (Rat.cast_le (K := ℝ)).mpr h1
    push_cast at h2
    linarith
  · intro n
    have h1 := (Rat.cast_le (K := ℝ)).mpr (maxOddProb_le_half n d)
    push_cast at h1
    linarith
