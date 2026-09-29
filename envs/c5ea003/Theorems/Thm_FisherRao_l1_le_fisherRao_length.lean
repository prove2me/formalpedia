-- Prove2me | Theorems.Thm_FisherRao_l1_le_fisherRao_length
-- name    : FisherRao.l1_le_fisherRao_length
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:33:13.957134+00:00
-- url     : https://prove2.me/theorems/28125311-b673-40a7-a605-bad87945e297
-- title:
--   The `L¹` bound integrates to a Fisher–Rao length bound.
-- statement:
--   **The `L¹` bound integrates to a Fisher–Rao length bound.**
--
--   Let `t ↦ p t` be a curve in the open probability simplex of a finite type `ι`, with
--   continuous velocity field `v` (so `v t i` is the derivative of `t ↦ p t i`).
--   Then the `L¹` distance between the endpoints `p a` and `p b` is at most the
--   Fisher–Rao length of the curve on `[a, b]`.
--
--   ```lean
--   theorem FisherRao.l1_le_fisherRao_length{p v : ℝ → ι → ℝ} {a b : ℝ} (hab : a ≤ b)
--       (hderiv : ∀ t i, HasDerivAt (fun s => p s i) (v t i) t)
--       (hv : ∀ i, Continuous fun t => v t i)
--       (hpos : ∀ t i, 0 < p t i) (hp1 : ∀ t, ∑ i, p t i = 1) :
--       l1Dist (p b) (p a) ≤ fisherRaoLength p v a b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/FisherRaoLength/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/FisherRaoLength/Core.lean#L130

-- Thm stub generated from Algebra/FisherRaoLength/Core.lean
import Mathlib
import Definitions.Def_Algebra_FisherRaoLength_Core
/-
# The `L¹` bound integrates to a Fisher–Rao length bound

This file proves the main theorem `l1_le_fisherRao_length`: along any smooth
curve of (strictly positive) probability vectors, the `L¹` distance between the
endpoints is bounded by the Fisher–Rao length of the curve.

The infinitesimal statement is a Cauchy–Schwarz inequality on the simplex,

  `∑ᵢ |vᵢ| = ∑ᵢ (|vᵢ| / √pᵢ) · √pᵢ ≤ √(∑ᵢ vᵢ²/pᵢ) · √(∑ᵢ pᵢ) = √(∑ᵢ vᵢ²/pᵢ)`,

i.e. the `L¹` speed of a curve of probability vectors never exceeds its
Fisher–Rao speed.  Integrating this pointwise bound with the fundamental theorem
of calculus turns it into the global length bound.

## Main definitions

* `l1Dist`            — the `L¹` distance `∑ᵢ |pᵢ - qᵢ|` (twice total variation)
* `fisherRaoSpeed`    — `√(∑ᵢ vᵢ² / pᵢ)`, the Fisher–Rao norm of a tangent vector
* `fisherRaoLength`   — the integral of the Fisher–Rao speed along a curve

## Main results

* `l1_speed_le_fisherRaoSpeed` — the infinitesimal (Cauchy–Schwarz) bound
* `l1_le_fisherRao_length`     — the integrated length bound (main theorem)
* `l1_le_fisherRao_length_uIcc`— localized version, hypotheses only on `[a,b]`
* `tv_le_half_fisherRao_length`— total variation form of the main theorem
* `fisherRaoSpeed_eq_two_mul_sqrtSpeed` — Fisher–Rao speed is twice the
  Euclidean speed of the square-root (sphere) embedding
* `TwoPoint.fisherRaoLength_eq_arcsin`, `TwoPoint.l1_lt_fisherRaoLength`,
  `TwoPoint.sharp` — an exactly solvable family showing the inequality is
  strict but that the constant `1` is optimal
* `fisherRao_sq_tensor`, `fisherRaoSpeed_tensor` — Pythagorean tensorization
* `abs_sub_event_le_half_fisherRao_length` — no event's probability moves by
  more than half the length
* `sqrt_chord_le_half_fisherRao_length` — the sharper spherical chord bound
* `one_sub_bhattacharyya_le_sq_fisherRao_length` — Hellinger/Bhattacharyya form
* `l1Dist_le_two_mul_sqrt_one_sub_bhattacharyya_sq`,
  `l1Dist_le_sum_arccos_bhattacharyya` — the smoothness-free discrete analogue
-/

open Finset BigOperators Real MeasureTheory intervalIntegral

open FisherRao

variable {ι : Type*} [Fintype ι]

/-! ## Definitions -/




/-! ## Elementary properties -/





/-! ## The infinitesimal bound: Cauchy–Schwarz on the simplex -/


/-! ## Continuity and integrability infrastructure -/


variable {p v : ℝ → ι → ℝ}





/-! ## The main theorem -/

theorem FisherRao.l1_le_fisherRao_length{p v : ℝ → ι → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ t i, HasDerivAt (fun s => p s i) (v t i) t)
    (hv : ∀ i, Continuous fun t => v t i)
    (hpos : ∀ t i, 0 < p t i) (hp1 : ∀ t, ∑ i, p t i = 1) :
    l1Dist (p b) (p a) ≤ fisherRaoLength p v a b := by sorry
