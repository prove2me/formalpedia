-- Prove2me | Theorems.Thm_dist_to_hyperplane_eq
-- name    : dist_to_hyperplane_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:41:09.713165+00:00
-- url     : https://prove2.me/theorems/ec687380-cad9-4241-a052-d647be82a22f
-- title:
--   Dist to hyperplane eq
-- statement:
--   Formal statement of `dist_to_hyperplane_eq` from the Aether Catalog (Tropical). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem dist_to_hyperplane_eq[FiniteDimensional ℝ E]
--       (u : E) (c : ℝ) (x : E) (hu : u ≠ 0) :
--       Metric.infDist x (affineHyperplane u c) = |⟪u, x⟫_ℝ - c| / ‖u‖ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/PolyhedralRobustness/HyperplaneDistance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/PolyhedralRobustness/HyperplaneDistance.lean#L51

-- Thm stub generated from Tropical/PolyhedralRobustness/HyperplaneDistance.lean
import Mathlib
import Definitions.Def_Tropical_PolyhedralRobustness_HyperplaneDistance

/-!
# Distance to Affine Hyperplanes and Halfspaces

This file proves the fundamental formula for the Euclidean distance from a point
to an affine hyperplane `{y | ⟪u, y⟫_ℝ = c}` in a finite-dimensional inner product space:

  `dist x {y | ⟪u, y⟫_ℝ = c} = |⟪u, x⟫_ℝ - c| / ‖u‖`

This is the atomic geometric lemma underlying polyhedral robustness certificates
for tropical/ReLU classifiers.

## Main Results

* `dist_to_hyperplane_eq` — exact distance from a point to an affine hyperplane
* `dist_to_tie_hyperplane_eq` — distance to the tie set of two affine forms
-/

open scoped InnerProductSpace
open Metric Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


/-
The hyperplane `{y | ⟪u, y⟫_ℝ = c}` is nonempty when `u ≠ 0`.
-/

/-
The hyperplane `{y | ⟪u, y⟫_ℝ = c}` is closed.
-/

/-
**Distance to affine hyperplane formula.**
The Euclidean distance from a point `x` to the hyperplane `{y | ⟪u, y⟫_ℝ = c}`
equals `|⟪u, x⟫_ℝ - c| / ‖u‖`, provided `u ≠ 0`.
-/

theorem dist_to_hyperplane_eq[FiniteDimensional ℝ E]
    (u : E) (c : ℝ) (x : E) (hu : u ≠ 0) :
    Metric.infDist x (affineHyperplane u c) = |⟪u, x⟫_ℝ - c| / ‖u‖ := by sorry
