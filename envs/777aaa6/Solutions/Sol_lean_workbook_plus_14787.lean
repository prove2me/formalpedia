-- Prove2me | solution 1 for lean_workbook_plus_14787
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:11.561205+00:00
-- url     : https://prove2.me/submissions/4cf2a7c1-7667-44e8-b6ea-946bcd0fa778

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) (hx : x - 1/x = 2) : x^2/(x^4 + 1) = 1/6 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
