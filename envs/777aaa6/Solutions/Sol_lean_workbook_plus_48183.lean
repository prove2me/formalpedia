-- Prove2me | solution 1 for lean_workbook_plus_48183
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:41.117995+00:00
-- url     : https://prove2.me/submissions/a90f4cfb-35c4-423a-9e9a-5f0a4a15ca5c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x:ℝ) : 6 * (x ^ 10 + x ^ 8) - 8 * x ^ 9 - 3 * x ^ 8 - 7 * x ^ 3 + 7 ≥ 4 * x ^ 9 - 3 * x ^ 8 - 7 * x ^ 3 + 7 := by
  intros
  have h : (0 : ℝ) ≤ (6 * (x ^ 10 + x ^ 8) - 8 * x ^ 9 - 3 * x ^ 8 - 7 * x ^ 3 + 7) - (4 * x ^ 9 - 3 * x ^ 8 - 7 * x ^ 3 + 7) := by
    calc
      0 ≤ (6 : ℝ) * (((x ^ 4) + ((-1) * (x ^ 5))))^2 := by positivity
      _ = (6 * (x ^ 10 + x ^ 8) - 8 * x ^ 9 - 3 * x ^ 8 - 7 * x ^ 3 + 7) - (4 * x ^ 9 - 3 * x ^ 8 - 7 * x ^ 3 + 7) := by ring
  exact sub_nonneg.mp h
