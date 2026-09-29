-- Prove2me | solution 1 for lean_workbook_plus_27100
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:15:20.811814+00:00
-- url     : https://prove2.me/submissions/0ec5f300-47c4-4ef6-8980-dee2fcef8697

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b x y : ℝ) : x = a + 1 ∧ y = b + 1 ↔ a = x - 1 ∧ b = y - 1 := by
  intros
  aesop (config := {maxRuleApplications := 120})
