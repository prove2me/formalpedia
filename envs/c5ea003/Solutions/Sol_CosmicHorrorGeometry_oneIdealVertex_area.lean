-- Prove2me | solution 1 for CosmicHorrorGeometry.oneIdealVertex_area
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:49.65579+00:00
-- url     : https://prove2.me/submissions/7f905b01-dd16-4578-808c-159f356357f6

-- Sol generated from Geometry/CosmicHorror/OneIdealVertex.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_OneIdealVertex
import Theorems.Thm_CosmicHorrorGeometry_chordHeight_pos
import Theorems.Thm_CosmicHorrorGeometry_integral_invSqrtChord_subinterval
import Theorems.Thm_CosmicHorrorGeometry_slicedArea_eq

/-!
# Gauss–Bonnet with one ideal vertex, derived from the metric

This file carries the programme of `HyperbolicIdealArea.lean` one step further.
There we computed the area of a *fully* ideal triangle (all three angles `0`).
Here we compute the area of a hyperbolic triangle with **one** ideal vertex and
two genuine finite vertices, and we do not postulate the interior angles: we
*define* them as angles between the tangent vectors of the two geodesic sides
and prove the Gauss–Bonnet identity

`area = (π - (α + β + 0)) / κ = hyperbolicArea κ α β 0`.

Because the half-plane metric `(dx² + dy²)/(κ y²)` is a pointwise positive
multiple of the Euclidean one, hyperbolic angles coincide with Euclidean
angles; this is recorded formally by `angleBetween_smul_left` and
`angleBetween_smul_right`, which say the angle functional is invariant under
positive rescaling of either tangent vector, hence under conformal change of
metric.

## The configuration

Fix `0 < φ < θ < π`.  The triangle has

* geodesic sides the two vertical rays `x = cos θ` and `x = cos φ` (these are
  half-plane geodesics), and the unit semicircle `|z| = 1` (also a geodesic);
* vertices `(cos θ, sin θ)`, `(cos φ, sin φ)` and the ideal point `∞`.

## Main results

* `angleBetween_vertical_circleRight`, `angleBetween_vertical_circleLeft`:  the
  interior angles are `π - θ` and `φ`.
* `oneIdealVertex_area`:  the hyperbolic area equals `(θ - φ)/κ`.  The result is
  proved for `0 ≤ φ < θ ≤ π`, so it covers one, two (`twoIdealVertices_area`)
  and three (`threeIdealVertices_area`) ideal vertices in one statement.
* `oneIdealVertex_gauss_bonnet`:  the area equals `hyperbolicArea κ α β 0`,
  the algebraic Gauss–Bonnet invariant evaluated at the two computed angles.
* `oneIdealVertex_angles_pos`:  both finite angles are *strictly* positive, so
  a triangle with a finite vertex is never ideal — angle sum `0` really does
  require adjoining the boundary.
* `oneIdealVertex_area_lt_ideal`:  consequently its area is strictly below the
  ideal maximum `π / κ`.
-/

open CosmicHorrorGeometry

open Real Set MeasureTheory Filter Topology

/-! ### Euclidean = hyperbolic angles -/









/-! ### The unit semicircle as the lower boundary -/


lemma arcsinChord_neg_one_one (x : ℝ) : arcsinChord (-1) 1 x = Real.arcsin x := by
  unfold arcsinChord
  norm_num

lemma arcsin_cos_of_mem {t : ℝ} (h0 : 0 ≤ t) (hpi : t ≤ π) :
    Real.arcsin (Real.cos t) = π / 2 - t := by
  rw [← Real.sin_pi_div_two_sub t]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith)

/-! ### The area of a triangle with one ideal vertex -/


lemma cos_lt_cos_of {φ θ : ℝ} (h0 : 0 ≤ φ) (hlt : φ < θ) (hpi : θ ≤ π) :
    Real.cos θ < Real.cos φ :=
  Real.cos_lt_cos_of_nonneg_of_le_pi h0 hpi hlt










open CosmicHorrorGeometry in
theorem solution{κ θ φ : ℝ} (hφ : 0 ≤ φ) (hφθ : φ < θ) (hθ : θ ≤ π) :
    oneIdealVertexArea κ θ φ = (θ - φ) / κ := by
  have hcc : Real.cos θ < Real.cos φ := cos_lt_cos_of hφ hφθ hθ
  have hlb : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hub : Real.cos φ ≤ 1 := Real.cos_le_one φ
  have hsub : Ioo (Real.cos θ) (Real.cos φ) ⊆ Ioo (-1 : ℝ) 1 := fun x hx =>
    ⟨lt_of_le_of_lt hlb hx.1, lt_of_lt_of_le hx.2 hub⟩
  rw [oneIdealVertexArea, slicedArea_eq hcc _ (fun x hx => chordHeight_pos (hsub hx))]
  congr 1
  rw [integral_invSqrtChord_subinterval (by norm_num : (-1 : ℝ) < 1) hlb hcc hub,
    arcsinChord_neg_one_one, arcsinChord_neg_one_one,
    arcsin_cos_of_mem hφ (by linarith), arcsin_cos_of_mem (by linarith) hθ]
  ring
