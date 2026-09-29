-- Prove2me | solution 1 for lean_workbook_plus_42611
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:07.831064+00:00
-- url     : https://prove2.me/submissions/7909e2a8-b55a-4daf-84ce-e3574c748887

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) : x + 2/x = y + 2/y → x*y = 2 := by
  intros
  grind
