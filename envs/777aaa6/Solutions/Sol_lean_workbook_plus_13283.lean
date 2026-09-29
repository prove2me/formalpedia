-- Prove2me | solution 1 for lean_workbook_plus_13283
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:34.719276+00:00
-- url     : https://prove2.me/submissions/c07884e2-cc2c-46bd-93b1-acf60980836e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, (a * b + b * c + a * c) ^ 2 ≥ 3 * a * b * c * (a + b + c) := by
  intro a b c
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
