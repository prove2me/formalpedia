-- Prove2me | solution 1 for lean_workbook_plus_65300
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:16:31.082327+00:00
-- url     : https://prove2.me/submissions/eacc887c-bb20-4042-8e40-6409fb953f36

import Mathlib
set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) : 2 * (x*y + y*z + z*x) ≤ 3*x*y*z + x + y + z   := by
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hy1 : 0 ≤ 1 - y := sub_nonneg.mpr hy.2
  have hz1 : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  have h1 : 0 ≤ x * (1 - y) * (1 - z) :=
    mul_nonneg (mul_nonneg hx.1 hy1) hz1
  have h2 : 0 ≤ y * (1 - z) * (1 - x) :=
    mul_nonneg (mul_nonneg hy.1 hz1) hx1
  have h3 : 0 ≤ z * (1 - x) * (1 - y) :=
    mul_nonneg (mul_nonneg hz.1 hx1) hy1
  nlinarith only [h1, h2, h3]

#print axioms solution
