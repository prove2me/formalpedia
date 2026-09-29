-- Prove2me | solution 1 for lean_workbook_plus_15528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:08.269613+00:00
-- url     : https://prove2.me/submissions/cb1dab7f-a1a3-4ed3-a1cc-1ecec22977d9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (habc : a + b + c = 0) : (a^2 + b^2 + c^2) / 2 * (a^5 + b^5 + c^5) / 5 = (a^7 + b^7 + c^7) / 7 := by
  intros
  grind
