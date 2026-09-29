-- Prove2me | solution 1 for CosmicHorrorGeometry.mobius_eq_id_of_fixes_zero_one_infty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:49.056715+00:00
-- url     : https://prove2.me/submissions/534b4971-ba00-43a2-9cc2-f3b6e7830c87

-- Sol generated from Geometry/CosmicHorror/HalfPlaneMobius.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HalfPlaneMobius
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea

/-!
# Boundary triples, real Möbius maps, and normalisation of ideal triangles

`HyperbolicIdealArea.lean` computes the hyperbolic area of the ideal triangle
whose vertices are two finite boundary points `a < b` and the boundary point
`∞`.  To know that this covers *every* ideal triangle one needs the classical
fact that the orientation-preserving isometry group of the half-plane model,
namely the real Möbius group `PSL(2, ℝ)`, acts **sharply three-transitively** on
the boundary circle `ℝ ∪ {∞}`.  This file proves exactly that, in an elementary
and fully explicit form, together with the two facts that make such maps
isometries of the hyperbolic plane:

* `mobius_im`:  `Im T(z) = det · Im z / ‖Cz + D‖²`, so a positive determinant
  forces the upper half-plane to be preserved (`mobius_mapsTo_upperHalfPlane`).
* `mobius_conformal_factor`:  `‖T'(z)‖ / Im T(z) = 1 / Im z`, i.e. `T` preserves
  the hyperbolic line element `|dz| / y` pointwise.  This is the infinitesimal
  statement of "`T` is a hyperbolic isometry".
* `exists_mobius_normalising`:  every triple `p < q < r` of finite boundary
  points is carried to the normal form `(0, 1, ∞)` by a real Möbius map of
  positive determinant, and `mobius_eq_id_of_fixes_zero_one_infty` shows that
  the normalising map is unique.  Hence three distinct boundary points do
  determine an ideal triangle, uniquely up to hyperbolic isometry.
-/

open CosmicHorrorGeometry

open Real Set Filter Topology Complex

/-! ### The real Möbius action -/







/-! ### Sharp three-transitivity on the boundary -/











open CosmicHorrorGeometry in
theorem solution{A B D : ℝ} (hD : D ≠ 0)
    (h0 : mobiusR A B 0 D 0 = 0) (h1 : mobiusR A B 0 D 1 = 1) :
    ∀ x : ℝ, mobiusR A B 0 D x = x := by
  have hB : B = 0 := by
    simp only [mobiusR, mul_zero, zero_add, div_eq_zero_iff] at h0
    tauto
  subst hB
  have hA : A = D := by
    simp only [mobiusR, mul_one, add_zero, zero_add] at h1
    exact (div_eq_one_iff_eq hD).1 h1
  subst hA
  intro x
  simp only [mobiusR, zero_mul, zero_add, add_zero]
  field_simp
