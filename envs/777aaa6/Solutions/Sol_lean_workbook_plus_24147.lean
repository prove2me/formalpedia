-- Prove2me | solution 1 for lean_workbook_plus_24147
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:15.042825+00:00
-- url     : https://prove2.me/submissions/3e809c90-9690-40f0-b21d-a3648ebf2e7b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : 3 * x^2 = 23) :
  x = Real.sqrt (23 / 3) ∨ x = -Real.sqrt (23 / 3) := by
  intros
  grind
