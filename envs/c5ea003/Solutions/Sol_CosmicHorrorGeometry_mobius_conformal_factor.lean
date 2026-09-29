-- Prove2me | solution 1 for CosmicHorrorGeometry.mobius_conformal_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:48.538922+00:00
-- url     : https://prove2.me/submissions/7cff0d0e-9a25-427d-a721-d66451f658b4

-- Sol generated from Geometry/CosmicHorror/HalfPlaneMobius.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HalfPlaneMobius
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Theorems.Thm_CosmicHorrorGeometry_mobius_mapsTo_upperHalfPlane

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



/-- **Imaginary part of a Möbius image.**  The determinant appears as the exact
distortion factor of the height coordinate. -/
theorem mobius_im (A B C D : ℝ) (z : ℂ) :
    (mobiusC A B C D z).im = (A * D - B * C) * z.im / Complex.normSq ((C : ℂ) * z + D) := by
  simp only [mobiusC, Complex.div_im, Complex.add_im, Complex.add_re, Complex.mul_im,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring




/-! ### Sharp three-transitivity on the boundary -/











open CosmicHorrorGeometry in
theorem solution{A B C D : ℝ} (hdet : 0 < A * D - B * C) {z : ℂ}
    (hz : 0 < z.im) :
    ‖((A : ℂ) * D - (B : ℂ) * C) / ((C : ℂ) * z + D) ^ 2‖ / (mobiusC A B C D z).im
      = 1 / z.im := by
  have hne : ((C : ℂ) * z + D) ≠ 0 := by
    intro h
    have := mobius_mapsTo_upperHalfPlane hdet hz
    rw [mobius_im, h] at this
    simp at this
  have hdetC : ((A : ℂ) * D - (B : ℂ) * C) = ((A * D - B * C : ℝ) : ℂ) := by push_cast; ring
  have hnorm : ‖((A : ℂ) * D - (B : ℂ) * C) / ((C : ℂ) * z + D) ^ 2‖
      = (A * D - B * C) / Complex.normSq ((C : ℂ) * z + D) := by
    rw [hdetC, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdet, norm_pow, Complex.sq_norm]
  rw [hnorm, mobius_im]
  have hns : 0 < Complex.normSq ((C : ℂ) * z + D) := Complex.normSq_pos.2 hne
  field_simp
