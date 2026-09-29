-- Prove2me | solution 1 for lean_workbook_plus_72093
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:41:51.074617+00:00
-- url     : https://prove2.me/submissions/0aad6dae-4c1a-4e02-81c8-2fef261b2182

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (hn : 0 < n) : ∃ a : ℕ → ℕ, (∀ i j : ℕ, i + j ≤ n → a i + a j ≤ n ∧ a (a i + a j) = a (i + j)) := by
  intros
  aesop (config := {maxRuleApplications := 120})
