-- Prove2me | solution 1 for lean_workbook_plus_52651
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:44.159675+00:00
-- url     : https://prove2.me/submissions/63a843d5-28ba-4bf7-a798-7160229a0e0b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (a + b + c) / 3 ≤ Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3) := by
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
