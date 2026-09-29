-- Prove2me | solution 1 for lean_workbook_plus_11269
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:15.074921+00:00
-- url     : https://prove2.me/submissions/ea26112d-a910-49bc-858a-f666c6780452

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (a : ℕ → ℕ) (h₁ : ∃ k : ℕ, a n = a (2^k + k - 2) ∧ a (2^k + k - 2) = (2^(k-1))^2) : ∃ m : ℕ, a n = m^2 := by
  intros
  aesop (config := {maxRuleApplications := 120})
