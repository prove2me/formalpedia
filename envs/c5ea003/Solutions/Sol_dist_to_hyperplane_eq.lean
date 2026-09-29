-- Prove2me | solution 1 for dist_to_hyperplane_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T10:21:04.368715+00:00
-- url     : https://prove2.me/submissions/56f21cc7-2021-49eb-bc07-d4c377e75d4d

-- Sol generated from Tropical/PolyhedralRobustness/HyperplaneDistance.lean
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
lemma affineHyperplane_nonempty [FiniteDimensional ℝ E] (u : E) (c : ℝ) (hu : u ≠ 0) :
    (affineHyperplane u c).Nonempty := by
      refine' ⟨ ( c / ‖u‖ ^ 2 ) • u, _ ⟩;
      unfold affineHyperplane;
      simp +decide [ inner_smul_right, hu, div_mul_cancel₀ ]

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


theorem solution[FiniteDimensional ℝ E]
    (u : E) (c : ℝ) (x : E) (hu : u ≠ 0) :
    Metric.infDist x (affineHyperplane u c) = |⟪u, x⟫_ℝ - c| / ‖u‖ := by
      refine' le_antisymm _ _;
      · -- Let $p = x + \frac{c - \langle u, x \rangle}{\|u\|^2} \cdot u$. Then $p$ lies on the hyperplane $\{y | \langle u, y \rangle = c\}$.
        obtain ⟨p, hp⟩ : ∃ p ∈ affineHyperplane u c, dist x p = abs (⟪u, x⟫_ℝ - c) / ‖u‖ := by
          refine' ⟨ x + ( c - ⟪u, x⟫_ℝ ) • ( ‖u‖ ^ 2 ) ⁻¹ • u, _, _ ⟩ <;> simp_all +decide [ affineHyperplane, inner_add_right, inner_smul_right ];
          simp +decide [ norm_smul, abs_sub_comm, div_eq_inv_mul, hu ];
          grind;
        exact hp.2 ▸ infDist_le_dist_of_mem hp.1;
      · -- By definition of infimum distance, we have:
        have h_infDist : ∀ y ∈ affineHyperplane u c, dist x y ≥ abs (⟪u, x⟫_ℝ - c) / ‖u‖ := by
          -- For any `y` in the hyperplane, we have `⟪u, y⟫ = c`.
          intro y hy
          have h_ortho : ⟪u, y⟫_ℝ = c := by
            exact hy;
          -- By Cauchy-Schwarz inequality, we have |⟪u, x - y⟫_ℝ| ≤ ‖u‖ * ‖x - y‖.
          have h_cauchy_schwarz : abs (⟪u, x - y⟫_ℝ) ≤ ‖u‖ * ‖x - y‖ := by
            exact abs_real_inner_le_norm u ( x - y );
          rw [ ge_iff_le, div_le_iff₀' ( norm_pos_iff.mpr hu ) ];
          simpa [ h_ortho, dist_eq_norm, inner_sub_right ] using h_cauchy_schwarz;
        rw [ infDist_eq_iInf ];
        refine' le_csInf _ _;
        · exact ⟨ _, ⟨ ⟨ Classical.choose ( affineHyperplane_nonempty u c hu ), Classical.choose_spec ( affineHyperplane_nonempty u c hu ) ⟩, rfl ⟩ ⟩;
        · aesop
