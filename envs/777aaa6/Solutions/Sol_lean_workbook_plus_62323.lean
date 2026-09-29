-- Prove2me | solution 1 for lean_workbook_plus_62323
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:43:02.843541+00:00
-- url     : https://prove2.me/submissions/d7cb4adc-37e8-4121-89fc-e637ad8f0ca1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) : Set.range f = {y : ℝ | ∃ x : ℝ, y = f x} := by
  intros
  aesop (config := {maxRuleApplications := 120})
