-- Prove2me | solution 1 for lean_workbook_plus_40945
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:43:09.007577+00:00
-- url     : https://prove2.me/submissions/a271aa98-327f-4fb2-b65f-9e7eefceea99

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (h : abs (a - b) < abs b / 2) : abs a > abs b / 2 := by
  intros
  grind
