-- Prove2me | solution 1 for lean_workbook_plus_23231
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:46.780375+00:00
-- url     : https://prove2.me/submissions/3c34c724-ea93-4d54-a5fc-6e9abc402651

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 / b^2 + b / (a + b) > 4 / 5 := by
  have hi : a^2/b^2+b/(a+b)-4/5=(5*a^3+5*b*(a-2*b/5)^2+b^3/5)/(5*b^2*(a+b)) := by field_simp; ring
  have hp : 0<(5*a^3+5*b*(a-2*b/5)^2+b^3/5)/(5*b^2*(a+b)) := by positivity
  linarith
