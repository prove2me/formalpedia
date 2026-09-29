-- Prove2me | solution 1 for lean_workbook_plus_55079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:22:04.962402+00:00
-- url     : https://prove2.me/submissions/9232fcc7-1b15-47b6-8aa4-7e2464123bd6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution {k m y : ℤ} (h₁ : k = 3*m) (h₂ : m*(12*m - 1) = y^2) : ∃ k m y : ℤ, k = 3*m ∧ m*(12*m - 1) = y^2 := by
  intros
  aesop (config := {maxRuleApplications := 120})
