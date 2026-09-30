-- Prove2me | solution 1 for Hirsch.common_face_diameter_of_dim_eq_four
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T02:55:13.787575+00:00
-- url     : https://prove2.me/submissions/344db8e0-f27e-4198-bd5e-7bda695dea75

import Theorems.Thm_Hirsch_common_face_larman_diameter
import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Set Hirsch HirschCommonFace

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hne : (commonFace a b u x).Nonempty)
    (hdim : commonFaceDim a b u x = 4) :
    DiamLE (commonFace a b u x) (2 * n) := by
  have hlar := common_face_larman_diameter a b u x hbd hne
  have hbud : n * 2 ^ (commonFaceDim a b u x - 3) = 2 * n := by
    rw [hdim]; ring
  rwa [hbud] at hlar

#print axioms solution
