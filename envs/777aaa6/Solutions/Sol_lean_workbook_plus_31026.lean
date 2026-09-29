-- Prove2me | solution 1 for lean_workbook_plus_31026
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:57.214004+00:00
-- url     : https://prove2.me/submissions/f486a6c5-152d-417b-8506-ef865ec76ddb

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 / b + b^2 / (2 * a + b) ≥ (a + b) / 2 := by
  have hB : b ≠ 0 := ne_of_gt hb
  have hD : 2*a+b ≠ 0 := ne_of_gt (by positivity)
  have hid : a^2/b+b^2/(2*a+b)-(a+b)/2 = (2*a-b)^2*(a+b)/(2*b*(2*a+b)) := by
    field_simp [hB,hD]
    <;> ring
  have hn : 0 ≤ (2*a-b)^2*(a+b)/(2*b*(2*a+b)) := by positivity
  linarith
