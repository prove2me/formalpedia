-- Prove2me | solution 1 for lean_workbook_plus_40178
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:43:11.418959+00:00
-- url     : https://prove2.me/submissions/c4768b27-678f-4ae3-92fc-4147acae3a1b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∃ f g : ℝ → ℝ, ∀ x, f x = 0 ∧ g x = 0 := by
  intros
  aesop (config := {maxRuleApplications := 120})
