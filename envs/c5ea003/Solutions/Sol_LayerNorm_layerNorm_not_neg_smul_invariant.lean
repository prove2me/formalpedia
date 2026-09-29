-- Prove2me | solution 1 for LayerNorm.layerNorm_not_neg_smul_invariant
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:07:23.948983+00:00
-- url     : https://prove2.me/submissions/5aacc703-8bd0-4897-a416-2376ad283461

-- Sol generated from MachineLearning/TransformerUniversality/LayerNorm.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_LayerNorm
import Theorems.Thm_LayerNorm_var_eq_zero_iff

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







/-! ### Basic identities -/



omit [Nonempty ι] in
theorem mean_smul (a : ℝ) (x : ι → ℝ) :
    mean (fun i => a * x i) = a * mean x := by
  simp only [mean, ← Finset.mul_sum]
  ring


omit [Nonempty ι] in
theorem var_smul (a : ℝ) (x : ι → ℝ) :
    var (fun i => a * x i) = a ^ 2 * var x := by
  simp only [var, mean_smul]
  rw [Finset.sum_congr rfl (g := fun i => a ^ 2 * (x i - mean x) ^ 2)
    (fun i _ => by ring), ← Finset.mul_sum]
  ring

theorem var_nonneg (x : ι → ℝ) : 0 ≤ var x := by
  apply div_nonneg _ (le_of_lt dim_pos)
  exact Finset.sum_nonneg fun i _ => sq_nonneg _



/-! ### The exact symmetry group of layer normalization -/



omit [Nonempty ι] in
/-- **Negative scalings flip the sign.**  Together with `layerNorm_pos_smul` this pins down
the symmetry group: shifts and positive dilations act trivially, negative dilations act by
`-1`. -/
theorem layerNorm_neg_smul (eps a : ℝ) (ha : a < 0) (x : ι → ℝ) :
    layerNorm (a ^ 2 * eps) (fun i => a * x i) = fun i => -(layerNorm eps x i) := by
  funext i
  simp only [layerNorm, mean_smul, var_smul]
  have hfac : a ^ 2 * var x + a ^ 2 * eps = a ^ 2 * (var x + eps) := by ring
  rw [hfac, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs, abs_of_neg ha]
  rw [show a * x i - a * mean x = a * (x i - mean x) by ring]
  rw [show -a * Real.sqrt (var x + eps) = (-a) * Real.sqrt (var x + eps) from rfl]
  rw [show a * (x i - mean x) = (-a) * (-(x i - mean x)) by ring]
  rw [mul_div_mul_left _ _ (by linarith : -a ≠ 0)]
  ring


/-! ### Moments of the normalized output -/







/-! ### Composition with the learned affine stage -/






open LayerNorm in
theorem solution(eps a : ℝ) (ha : a < 0) (x : ι → ℝ)
    (heps : 0 ≤ eps) (hx : var x ≠ 0) :
    layerNorm (a ^ 2 * eps) (fun i => a * x i) ≠ layerNorm eps x := by
  intro hcontra
  rw [layerNorm_neg_smul eps a ha x] at hcontra
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ mean x := by
    by_contra hall
    push_neg at hall
    exact hx ((var_eq_zero_iff x).mpr hall)
  have hval := congrFun hcontra i
  have hvpos : 0 < var x + eps := lt_of_lt_of_le (lt_of_le_of_ne (var_nonneg x) (Ne.symm hx))
    (by linarith)
  have hs : 0 < Real.sqrt (var x + eps) := Real.sqrt_pos.mpr hvpos
  simp only [layerNorm] at hval
  have : (x i - mean x) / Real.sqrt (var x + eps) = 0 := by linarith [hval]
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · exact hi (by linarith)
  · exact absurd h (ne_of_gt hs)
