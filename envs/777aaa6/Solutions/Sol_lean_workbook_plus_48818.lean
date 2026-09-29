-- Prove2me | solution 1 for lean_workbook_plus_48818
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:27.337628+00:00
-- url     : https://prove2.me/submissions/cc35951d-eb69-4f68-9258-9ed3bbee4f8f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : Real.sqrt (a ^ 2 - a * b + b ^ 2) ≥ (1 / 2) * (a + b) := by
  intros
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
