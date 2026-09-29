-- Prove2me | solution 1 for lean_workbook_plus_35540
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:33.53081+00:00
-- url     : https://prove2.me/submissions/869892d0-6ea2-49d2-b890-fcaad01f6840

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 2 ≤ x) : (3 * x ^ 2 * (x ^ 2 - 4) + x ^ 2 + 4) / (2 * x * (x ^ 2 - 1) ^ 3) > 0 := by
  have hx0 : 0 < x := by linarith
  have hx4 : 0 ≤ x^2-4 := by nlinarith
  have hx1 : 0 < x^2-1 := by nlinarith
  have hn : 0 < 3*x^2*(x^2-4)+x^2+4 := by positivity
  exact div_pos hn (by positivity)
