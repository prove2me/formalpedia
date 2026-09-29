-- Prove2me | solution 1 for lean_workbook_plus_77864
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:03:02.138716+00:00
-- url     : https://prove2.me/submissions/2521d466-c823-4167-be5c-40ad8e8debd6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∃ a b : ℝ, a ≤ 1 ∧ b ≥ 1 ∧ (1 - a) * (1 - b) ≤ 1 := by
  intros
  aesop (config := {maxRuleApplications := 120})
