-- Prove2me | solution 1 for lean_workbook_plus_59345
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:18.326221+00:00
-- url     : https://prove2.me/submissions/a3e78cf8-3ea5-41c6-8d2e-98d65c4b0233

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x^4 - 4*x^3 + 6*x^2 - 4*x + 1 = 0) : x = 1 := by
  intros
  grind
