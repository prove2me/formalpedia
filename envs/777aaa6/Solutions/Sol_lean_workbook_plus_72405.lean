-- Prove2me | solution 1 for lean_workbook_plus_72405
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:39.471464+00:00
-- url     : https://prove2.me/submissions/68524d44-8ca0-4b26-93ea-e3e7e25791c8

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) ≤ 1 := by
  have hA : a*b+a+1 ≠ 0 := ne_of_gt (by positivity)
  have hB : b*c+b+1 ≠ 0 := ne_of_gt (by positivity)
  have hC : c*a+c+1 ≠ 0 := ne_of_gt (by positivity)
  have hid : a/(a*b+a+1)+b/(b*c+b+1)+c/(c*a+c+1) = 1-(a*b*c-1)^2/((a*b+a+1)*(b*c+b+1)*(c*a+c+1)) := by
    field_simp [hA,hB,hC]
    <;> ring
  have hn : 0 ≤ (a*b*c-1)^2/((a*b+a+1)*(b*c+b+1)*(c*a+c+1)) := by positivity
  linarith
