-- Prove2me | Definitions.Def_Tropical_PolyhedralRobustness_HyperplaneDistance
-- name    : Tropical_PolyhedralRobustness_HyperplaneDistance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:29.727199+00:00
-- url     : https://prove2.me/theorems/326b0285-eb28-4630-9af2-2c5f4363275d
-- title:
--   Aether Catalog definitions — Tropical_PolyhedralRobustness_HyperplaneDistance
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.PolyhedralRobustness.HyperplaneDistance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/PolyhedralRobustness/HyperplaneDistance.lean by skeleton subtraction
import Mathlib

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

/-- The affine hyperplane `{y | ⟪u, y⟫_ℝ = c}`. -/
def affineHyperplane (u : E) (c : ℝ) : Set E :=
  {y : E | ⟪u, y⟫_ℝ = c}

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

/-
Variant: distance to the "tie hyperplane" of two affine forms.
Given affine forms `ℓ₁(y) = ⟪a₁, y⟫ + b₁` and `ℓ₂(y) = ⟪a₂, y⟫ + b₂`,
the tie set `{y | ℓ₁(y) = ℓ₂(y)}` is a hyperplane with normal `a₁ - a₂`.
The distance from `x` to this tie set is `|ℓ₁(x) - ℓ₂(x)| / ‖a₁ - a₂‖`.
-/

end


