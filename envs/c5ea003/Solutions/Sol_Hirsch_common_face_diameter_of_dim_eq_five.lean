-- Prove2me | solution 1 for Hirsch.common_face_diameter_of_dim_eq_five
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T03:07:51.498696+00:00
-- url     : https://prove2.me/submissions/965caa49-7961-4903-a8de-7589ffaefe69

import Theorems.Thm_Hirsch_common_face_larman_diameter
import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Set Hirsch HirschCommonFace

/-- When the common-face dimension is exactly five, Larman's coordinate bound
is `n * 2^{5-3} = 4n`. This is polynomial in `(n+d)` for this fixed dimension
and is not claimed as a uniform polynomial for unbounded `h`. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hne : (commonFace a b u x).Nonempty)
    (hdim : commonFaceDim a b u x = 5) :
    DiamLE (commonFace a b u x) (4 * n) := by
  have hlar := common_face_larman_diameter a b u x hbd hne
  have hbud : n * 2 ^ (commonFaceDim a b u x - 3) = 4 * n := by
    rw [hdim]; ring
  rwa [hbud] at hlar

#print axioms solution
