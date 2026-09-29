-- Prove2me | solution 1 for LayerNorm.var_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:03:41.726659+00:00
-- url     : https://prove2.me/submissions/d2b1988a-94d6-4bd1-bec0-9c558274ed80

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







theorem sum_sq_centered (x : ι → ℝ) :
    ∑ i, (x i - mean x) ^ 2 = dim ι * var x := by
  have h : dim ι ≠ 0 := dim_ne_zero
  rw [var]
  field_simp


/-! ### The exact symmetry group of layer normalization -/





/-! ### Moments of the normalized output -/







/-! ### Composition with the learned affine stage -/






open LayerNorm in
theorem solution(x : ι → ℝ) : var x = 0 ↔ ∀ i, x i = mean x := by
  constructor
  · intro h i
    have hs : ∑ j, (x j - mean x) ^ 2 = 0 := by
      rw [sum_sq_centered, h, mul_zero]
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (x j - mean x))).mp hs i (Finset.mem_univ i)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro h
    simp only [var]
    rw [Finset.sum_eq_zero fun i _ => by rw [h i]; ring, zero_div]
