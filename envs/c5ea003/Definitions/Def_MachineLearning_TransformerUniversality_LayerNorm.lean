-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_LayerNorm
-- name    : MachineLearning_TransformerUniversality_LayerNorm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:32.985971+00:00
-- url     : https://prove2.me/theorems/8e12b80a-0318-4735-a202-5f0d420fb0a7
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_LayerNorm
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.LayerNorm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/LayerNorm.lean by skeleton subtraction
import Mathlib

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

namespace LayerNorm

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Number of coordinates, as a real number. -/
noncomputable def dim (ι : Type*) [Fintype ι] : ℝ := (Fintype.card ι : ℝ)



/-- Coordinatewise mean of a feature vector. -/
noncomputable def mean (x : ι → ℝ) : ℝ := (∑ i, x i) / dim ι

/-- Coordinatewise (population) variance of a feature vector. -/
noncomputable def var (x : ι → ℝ) : ℝ := (∑ i, (x i - mean x) ^ 2) / dim ι

/-- Layer normalization with numerical stabilizer `ε`: centre, then divide by
`√(variance + ε)`. -/
noncomputable def layerNorm (eps : ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => (x i - mean x) / Real.sqrt (var x + eps)

/-- The learned affine stage, as in the catalog transformer file. -/
def affineNorm (scale bias x : ι → ℝ) : ι → ℝ := fun i => scale i * x i + bias i

/-- Standard full layer normalization: nonlinear normalization followed by a learned
coordinatewise affine map. -/
noncomputable def fullLayerNorm (scale bias : ι → ℝ) (eps : ℝ) (x : ι → ℝ) : ι → ℝ :=
  affineNorm scale bias (layerNorm eps x)

/-! ### Basic identities -/









/-! ### The exact symmetry group of layer normalization -/





/-! ### Moments of the normalized output -/







/-! ### Composition with the learned affine stage -/





end LayerNorm


