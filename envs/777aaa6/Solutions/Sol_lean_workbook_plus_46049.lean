-- Prove2me | solution 1 for lean_workbook_plus_46049
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:43:20.549908+00:00
-- url     : https://prove2.me/submissions/a786a10e-b1cd-4d65-afee-7f36de212fae

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x : ℝ, 0.6 < x ∧ x < 1 → x - x^3 < 0.6 := by
  intro x
  intros
  nlinarith [sq_nonneg x]
