-- Prove2me | solution 1 for lean_workbook_plus_58714
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:37.396128+00:00
-- url     : https://prove2.me/submissions/6b93e6d9-e708-43df-b7ff-453492643cd4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x : ℝ, x^4 + 3*x^2 - 6*x + 10 = 0 → x = 1 ∨ x = -1 ∨ x = 2 ∨ x = -2 := by
  intro x hx
  have hpos : 0 < x^4 + 3*x^2 - 6*x + 10 := by nlinarith [sq_nonneg (x^2), sq_nonneg (x-1)]
  have hfalse : False := by linarith
  exact hfalse.elim
