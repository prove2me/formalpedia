-- Prove2me | solution 1 for lean_workbook_plus_51685
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:13:51.80556+00:00
-- url     : https://prove2.me/submissions/0f01b14b-7db8-41bc-8124-821e3347b8dc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℤ) : ∃ n, n ≤ x ∧ x < n + 1 := by
  intros
  aesop (config := {maxRuleApplications := 120})
