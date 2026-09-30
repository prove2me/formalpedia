-- Prove2me | solution 1 for lean_workbook_plus_77111
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:39:51.085988+00:00
-- url     : https://prove2.me/submissions/12f2ece4-f3d1-4a23-bfc9-e6deba5aa519

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

private theorem cubic_mean_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    27*a*b*c ≤ (a+b+c)^3 := by
  have h1 : 0 ≤ (a+b+c)*((a-b)^2+(b-c)^2+(c-a)^2) := by positivity
  have h2 : 0 ≤ a*(b-c)^2+b*(c-a)^2+c*(a-b)^2 := by positivity
  nlinarith only [h1, h2]

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (habc : x*y*z = 8) : 1/(x^2+2)+1/(y^2+2)+1/(z^2+2) ≥ 1/2 := by
  have hprod : x^2*y^2*z^2 = 64 := by
    nlinarith only [congrArg (fun t : ℝ => t^2) habc]
  have hcube : (12:ℝ)^3 ≤ (x^2+y^2+z^2)^3 := by
    nlinarith only [cubic_mean_bound (x^2) (y^2) (z^2)
      (sq_nonneg x) (sq_nonneg y) (sq_nonneg z), hprod]
  have hsum : 12 ≤ x^2+y^2+z^2 :=
    le_of_pow_le_pow_left₀ (by decide : (3:ℕ) ≠ 0) (by positivity) hcube
  have h1 : 0 < x^2+2 := by positivity
  have h2 : 0 < y^2+2 := by positivity
  have h3 : 0 < z^2+2 := by positivity
  have hid : 1/(x^2+2)+1/(y^2+2)+1/(z^2+2)-1/2 =
      2*(x^2+y^2+z^2-12)/((x^2+2)*(y^2+2)*(z^2+2)) := by
    field_simp [ne_of_gt h1, ne_of_gt h2, ne_of_gt h3]
    linear_combination -hprod
  have hn : 0 ≤ 2*(x^2+y^2+z^2-12)/((x^2+2)*(y^2+2)*(z^2+2)) := by
    apply div_nonneg
    · exact mul_nonneg (by norm_num) (sub_nonneg.mpr hsum)
    · positivity
  linarith only [hid, hn]
