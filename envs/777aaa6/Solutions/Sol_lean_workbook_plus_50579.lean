-- Prove2me | solution 1 for lean_workbook_plus_50579
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:53.373322+00:00
-- url     : https://prove2.me/submissions/2c632b3e-915e-46e5-acc5-5bb0e0cbbc59

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (P : ℕ → ℕ) (hP : ∃ P₁ P₂ : ℕ → ℕ, ∀ n, P n = P₁ n + 2 * P₂ n) : ∃ n₁ n₂ : ℕ, P 2 = n₁ + 2 * n₂ := by
  intros
  aesop (config := {maxRuleApplications := 120})
