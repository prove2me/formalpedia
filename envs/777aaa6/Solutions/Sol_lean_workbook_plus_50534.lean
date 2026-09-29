-- Prove2me | solution 1 for lean_workbook_plus_50534
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:34:20.232265+00:00
-- url     : https://prove2.me/submissions/c74d3d21-63a8-46d7-bda1-d52090ff8ab1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} : 2 * (a ^ 8 - a ^ 6 * b ^ 2 - a ^ 6 * c ^ 2 + a ^ 4 * b ^ 2 * c ^ 2) + 2 * (b ^ 8 - b ^ 6 * c ^ 2 - b ^ 6 * a ^ 2 + b ^ 4 * c ^ 2 * a ^ 2) + 2 * (c ^ 8 - c ^ 6 * a ^ 2 - c ^ 6 * b ^ 2 + c ^ 4 * a ^ 2 * b ^ 2) ≥ 0 := by
  have hsorted (x y z : ℝ) (hz : 0 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
      0 ≤ x^4-x^3*y-x^3*z+x^2*y*z + (y^4-y^3*z-y^3*x+y^2*z*x) + (z^4-z^3*x-z^3*y+z^2*x*y) := by
    have hy : 0 ≤ y := le_trans hz hzy
    have hx : 0 ≤ x := le_trans hy hyx
    have hxz : z ≤ x := le_trans hzy hyx
    have hcoef : 0 ≤ x^2+x*y+y^2-z*(x+y) := by
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hxz), mul_nonneg hy (sub_nonneg.mpr hzy), mul_nonneg hx hy]
    have ht := mul_nonneg (mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hxz)) (sub_nonneg.mpr hzy)
    nlinarith only [mul_nonneg (sq_nonneg (x-y)) hcoef, ht]
  rcases le_total (a^2) (b^2) with hab | hba
  · rcases le_total (b^2) (c^2) with hbc | hcb
    · nlinarith only [hsorted (c^2) (b^2) (a^2) (sq_nonneg a) hab hbc]
    · rcases le_total (a^2) (c^2) with hac | hca
      · nlinarith only [hsorted (b^2) (c^2) (a^2) (sq_nonneg a) hac hcb]
      · nlinarith only [hsorted (b^2) (a^2) (c^2) (sq_nonneg c) hca hab]
  · rcases le_total (a^2) (c^2) with hac | hca
    · nlinarith only [hsorted (c^2) (a^2) (b^2) (sq_nonneg b) hba hac]
    · rcases le_total (b^2) (c^2) with hbc | hcb
      · nlinarith only [hsorted (a^2) (c^2) (b^2) (sq_nonneg b) hbc hca]
      · nlinarith only [hsorted (a^2) (b^2) (c^2) (sq_nonneg c) hcb hba]
