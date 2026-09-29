-- Prove2me | Theorems.Thm_LayerNorm_var_layerNorm_eq_one
-- name    : LayerNorm.var_layerNorm_eq_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:41:47.616407+00:00
-- url     : https://prove2.me/theorems/98790cb9-c29f-433a-86a6-ab179064cc1a
-- title:
--   Unit variance.
-- statement:
--   **Unit variance.**  With no stabilizer, a nonconstant input is mapped to a vector of
--   variance exactly one.
--
--   ```lean
--   theorem LayerNorm.var_layerNorm_eq_one(x : ι → ℝ) (hx : var x ≠ 0) :
--       var (layerNorm 0 x) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/LayerNorm.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/LayerNorm.lean#L198

-- Thm stub generated from MachineLearning/TransformerUniversality/LayerNorm.lean
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









/-! ### Basic identities -/









/-! ### The exact symmetry group of layer normalization -/





/-! ### Moments of the normalized output -/

theorem LayerNorm.var_layerNorm_eq_one(x : ι → ℝ) (hx : var x ≠ 0) :
    var (layerNorm 0 x) = 1 := by sorry
