-- Prove2me | solution 1 for lean_workbook_plus_11733
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:36.270139+00:00
-- url     : https://prove2.me/submissions/8c1b03c1-4215-40b2-a0d1-5f94cf152c89

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (F : ℕ → ℕ) (h₁ : F 1 = 1 ∧ F 2 = 1) (h₂ : ∀ n, F (n + 2) = F (n + 1) + F n) : F 8 = 21 := by
  intros
  aesop (config := {maxRuleApplications := 120})
