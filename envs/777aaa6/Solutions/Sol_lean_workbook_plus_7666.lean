-- Prove2me | solution 1 for lean_workbook_plus_7666
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:44.421922+00:00
-- url     : https://prove2.me/submissions/50ca4852-9601-42d2-bc54-5792d710a4c8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ (x y z : ℝ), 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ (x + y + z) ^ 2 := by
  intro x y z
  nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
