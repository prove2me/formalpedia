-- Prove2me | solution 1 for LayerNorm.var_layerNorm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:07:24.453234+00:00
-- url     : https://prove2.me/submissions/6cf90496-3fdd-4b3f-b994-654e62cf5592

-- Sol generated from MachineLearning/TransformerUniversality/LayerNorm.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_LayerNorm

/-!
# Full layer normalization: centering, variance scaling, and the learned affine stage

The catalog file `Catalog/MachineLearning/TransformerArchitecture.lean` deliberately
formalizes only the *learned affine* part of layer normalization (`affineNorm`), noting that
the data-dependent centering and variance normalization is a different, nonlinear operation.

This file adds the missing nonlinear stage and studies its exact symmetry group:

* `layerNorm_shift_invariant` — invariance under adding a constant to every coordinate;
* `layerNorm_pos_smul` — invariance under positive rescaling (with the ε-budget rescaled
  accordingly), and `layerNorm_neg_smul` showing that a negative scaling flips the sign, so
  the invariance group is exactly the shifts and the *positive* dilations;
* `layerNorm_not_neg_smul_invariant` — the sharp boundary: for a nonconstant input the
  negative-scaling symmetry genuinely fails;
* `sum_layerNorm_eq_zero`, `sum_sq_layerNorm` — the output has mean zero and second moment
  `n * v / (v + ε)`, hence exactly unit variance at `ε = 0`;
* `layerNorm_idempotent` — layer normalization is idempotent on nonconstant inputs;
* `fullLayerNorm_shift_invariant`, `fullLayerNorm_comp_affine` — composing the nonlinear
  normalization with the learned affine stage of the catalog file.
-/

open scoped BigOperators

open LayerNorm

variable {ι : Type*} [Fintype ι] [Nonempty ι]


theorem dim_pos : 0 < dim ι := by
  have h : 0 < Fintype.card ι := Fintype.card_pos
  simpa [dim] using (by exact_mod_cast h : (0:ℝ) < (Fintype.card ι : ℝ))

theorem dim_ne_zero : (dim ι) ≠ 0 := ne_of_gt dim_pos






/-! ### Basic identities -/

theorem sum_centered (x : ι → ℝ) : ∑ i, (x i - mean x) = 0 := by
  have h : dim ι ≠ 0 := dim_ne_zero
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mean, dim] at h ⊢
  field_simp
  ring





theorem var_nonneg (x : ι → ℝ) : 0 ≤ var x := by
  apply div_nonneg _ (le_of_lt dim_pos)
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem sum_sq_centered (x : ι → ℝ) :
    ∑ i, (x i - mean x) ^ 2 = dim ι * var x := by
  have h : dim ι ≠ 0 := dim_ne_zero
  rw [var]
  field_simp


/-! ### The exact symmetry group of layer normalization -/





/-! ### Moments of the normalized output -/

/-- The normalized output has mean zero. -/
theorem sum_layerNorm_eq_zero (eps : ℝ) (x : ι → ℝ) :
    ∑ i, layerNorm eps x i = 0 := by
  simp only [layerNorm, ← Finset.sum_div, sum_centered, zero_div]

theorem mean_layerNorm (eps : ℝ) (x : ι → ℝ) : mean (layerNorm eps x) = 0 := by
  rw [mean, sum_layerNorm_eq_zero, zero_div]

/-- The second moment of the normalized output is `n · v / (v + ε)`. -/
theorem sum_sq_layerNorm (eps : ℝ) (x : ι → ℝ) (h : 0 < var x + eps) :
    ∑ i, (layerNorm eps x i) ^ 2 = dim ι * var x / (var x + eps) := by
  simp only [layerNorm, div_pow]
  rw [Real.sq_sqrt (le_of_lt h), ← Finset.sum_div, sum_sq_centered]




/-! ### Composition with the learned affine stage -/






open LayerNorm in
theorem solution(x : ι → ℝ) (hx : var x ≠ 0) :
    var (layerNorm 0 x) = 1 := by
  have hpos : 0 < var x + 0 := by
    have := var_nonneg x
    cases lt_or_eq_of_le this with
    | inl h => linarith
    | inr h => exact absurd h.symm hx
  have hsum := sum_sq_layerNorm 0 x hpos
  simp only [var, mean_layerNorm, sub_zero]
  rw [hsum]
  have h : dim ι ≠ 0 := dim_ne_zero
  field_simp
  ring
