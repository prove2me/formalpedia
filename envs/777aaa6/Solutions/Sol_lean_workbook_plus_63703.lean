-- Prove2me | solution 1 for lean_workbook_plus_63703
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:43:29.505924+00:00
-- url     : https://prove2.me/submissions/48445232-5d04-4209-92da-fd32de63bd06

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
