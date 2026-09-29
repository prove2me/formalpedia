-- Prove2me | solution 1 for lean_workbook_plus_49682
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:42:41.464581+00:00
-- url     : https://prove2.me/submissions/1f1545d2-091d-4bd7-a5b1-1c14a6139efb

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (t : ℝ) (ht : 2 ≤ t) : (7 - 2 * t) ^ 3 ≤ 3 * (t ^ 2 - 1) ^ 2 := by
  have h : 0 ≤ t-2 := by linarith
  have h2 := sq_nonneg (t-2)
  have h3 := pow_nonneg h 3
  have h4 := pow_nonneg h 4
  nlinarith only [h,h2,h3,h4]
