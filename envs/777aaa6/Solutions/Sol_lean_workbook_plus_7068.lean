-- Prove2me | solution 1 for lean_workbook_plus_7068
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:00:24.416575+00:00
-- url     : https://prove2.me/submissions/5f49e070-1969-46f2-98ac-bd3bc947bc26

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a b c d : ℝ) (hab : a * b * c * d = 1) : 8 + (a^2 + b^2) * (c^2 + d^2) ≥ 3 * (a + b) * (c + d) := by
  nlinarith [sq_nonneg (a * c + b * d - 2), sq_nonneg (a * d + b * c - 2), sq_nonneg (a * c - b * d), sq_nonneg (a * d - b * c)]
