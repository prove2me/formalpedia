-- Prove2me | solution 1 for AffineStats.tendsto_one_sub_inv_pow_pred
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:58:15.948666+00:00
-- url     : https://prove2.me/submissions/146d169c-c326-4211-8f13-648ce30849be

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
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
theorem solution:
    Tendsto (fun N : ℕ => (((N : ℝ) - 1) / N) ^ (N - 1)) atTop (nhds (Real.exp (-1))) := by
  have h1 : Tendsto (fun N : ℕ => (1 + (-1 : ℝ) / N) ^ N) atTop (nhds (Real.exp (-1))) :=
    Real.tendsto_one_add_div_pow_exp (-1)
  have h2 : Tendsto (fun N : ℕ => (1 + (-1 : ℝ) / N)) atTop (nhds 1) := by
    have h0 : Tendsto (fun N : ℕ => (-1 : ℝ) / N) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (-1)
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add h0
  have h3 := h1.div h2 one_ne_zero
  rw [div_one] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by
    have hpos : 0 < N := by omega
    exact_mod_cast hpos
  have h2N : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hne : ((N : ℝ) - 1) / N ≠ 0 := div_ne_zero (by linarith) (ne_of_gt hN0)
  have heq : (1 + (-1 : ℝ) / N) = ((N : ℝ) - 1) / N := by field_simp; ring
  simp only [Pi.div_apply, heq]
  rw [div_eq_iff hne, ← pow_succ]
  congr 1
  omega
