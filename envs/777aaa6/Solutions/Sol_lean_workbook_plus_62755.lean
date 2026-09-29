-- Prove2me | solution 1 for lean_workbook_plus_62755
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:08.820685+00:00
-- url     : https://prove2.me/submissions/66181e01-4a77-43bc-8b38-6545eb262a90

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) (h : a^2 - 4*a + 3 = 0) : a = 1 ∨ a = 3 := by
  intros
  grind
