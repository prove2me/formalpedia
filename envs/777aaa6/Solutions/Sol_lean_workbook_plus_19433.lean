-- Prove2me | solution 1 for lean_workbook_plus_19433
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:54.288565+00:00
-- url     : https://prove2.me/submissions/d5d22d37-a719-42e9-8c40-faefb813b9d6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℕ → ℕ) (h₁ : ∀ n, a n = 2 * b n) : a = fun n ↦ 2 * b n := by
  intros
  aesop (config := {maxRuleApplications := 120})
