-- Prove2me | solution 1 for lean_workbook_plus_61096
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:57:45.596243+00:00
-- url     : https://prove2.me/submissions/e2c7e37d-c445-428f-a122-17d4635585f8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) (f : ℝ → ℝ) (hf: f = fun x => a * x + b) : a = -1 ∧ b = -2 → f = fun x => -x - 2 := by
  intros
  aesop (config := {maxRuleApplications := 120})
