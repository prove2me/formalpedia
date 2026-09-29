-- Prove2me | solution 1 for AffineStats.maxFlatProb_one_ge_limit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:58:13.692836+00:00
-- url     : https://prove2.me/submissions/3026f761-21d7-406d-96ca-731715da8054

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_exists_flatProb_one_ge_opt
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
theorem solution(d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ A : Finset (Vec n),
      ((((2 : ℝ) ^ (d + 1) - 1) / 2 ^ (d + 1)) ^ (2 ^ (d + 1) - 1) : ℝ) - ε
        ≤ ((flatProb n (d + 1) A 1 : ℚ) : ℝ) := by
  set L := ((((2 : ℝ) ^ (d + 1) - 1) / 2 ^ (d + 1)) ^ (2 ^ (d + 1) - 1) : ℝ) with hL
  have hbase : (0 : ℝ) ≤ ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ (d + 1) := by
    apply div_nonneg _ (by positivity)
    have : (1 : ℝ) ≤ 2 ^ (d + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hL1 : L ≤ 1 := by
    rw [hL]
    refine pow_le_one₀ hbase ?_
    rw [div_le_one (by positivity)]
    linarith
  -- choose `N` so that `(2^{d+1}-1)/2ᴺ < ε`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ N < ε := by
    have hzero : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ n)
        Filter.atTop (nhds 0) := by
      have hgeom : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have hrw : (fun n : ℕ => ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ n)
          = fun n : ℕ => ((2 : ℝ) ^ (d + 1) - 1) * ((1 / 2) ^ n) := by
        funext n; rw [div_pow, one_pow]; field_simp
      rw [hrw]
      simpa using hgeom.const_mul ((2 : ℝ) ^ (d + 1) - 1)
    exact (hzero.eventually (gt_mem_nhds hε)).exists
  refine ⟨max N (d + 1), fun n hn => ?_⟩
  have hdn : d + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hNn : N ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨A, hA⟩ := exists_flatProb_one_ge_opt n d hdn
  refine ⟨A, ?_⟩
  have hAR := (Rat.cast_le (K := ℝ)).mpr hA
  push_cast at hAR
  have hd1 : (1 : ℝ) ≤ 2 ^ (d + 1) := one_le_pow₀ (by norm_num)
  have herr : ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ n ≤ ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ N := by
    refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
    exact pow_le_pow_right₀ (by norm_num) hNn
  have herr2 : (0 : ℝ) ≤ ((2 : ℝ) ^ (d + 1) - 1) / 2 ^ n := by
    apply div_nonneg _ (by positivity)
    linarith
  nlinarith [hAR, hL0, hL1, herr, herr2]
