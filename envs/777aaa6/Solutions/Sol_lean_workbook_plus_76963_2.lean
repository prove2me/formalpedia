-- Prove2me | solution 2 for lean_workbook_plus_76963
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:18.220275+00:00
-- url     : https://prove2.me/submissions/b1d2051d-17f8-4bad-8851-52929b57b102

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

private theorem minimum_case (x y z : ℝ) (hx : 0 ≤ x)
    (hxy : x ≤ y) (hxz : x ≤ z) :
    0 ≤ x^3 + y^3 + z^3 + x^2*y + y^2*z + z^2*x -
      2*(x*y^2 + y*z^2 + z*x^2) := by
  have hu : 0 ≤ y-x := sub_nonneg.mpr hxy
  have hv : 0 ≤ z-x := sub_nonneg.mpr hxz
  have hn : 0 ≤ x*(y-x)^2 + x*(z-x)^2 + x*((y-x)-(z-x))^2 +
      (y-x)^3 + (z-x)*((z-x)-(y-x))^2 := by positivity
  nlinarith only [hn]

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x^3 + y^3 + z^3 + x^2*y + y^2*z + z^2*x -
      2*(x*y^2 + y*z^2 + z*x^2)) / (x+y) / (y+z) / (z+x) ≥ 0 := by
  have hn : 0 ≤ x^3 + y^3 + z^3 + x^2*y + y^2*z + z^2*x -
      2*(x*y^2 + y*z^2 + z*x^2) := by
    rcases le_total x y with hxy | hyx
    · rcases le_total x z with hxz | hzx
      · exact minimum_case x y z hx.le hxy hxz
      · nlinarith only [minimum_case z x y hz.le hzx (hzx.trans hxy)]
    · rcases le_total y z with hyz | hzy
      · nlinarith only [minimum_case y z x hy.le hyz hyx]
      · nlinarith only [minimum_case z x y hz.le (hzy.trans hyx) hzy]
  exact div_nonneg (div_nonneg (div_nonneg hn (add_pos hx hy).le)
    (add_pos hy hz).le) (add_pos hz hx).le
