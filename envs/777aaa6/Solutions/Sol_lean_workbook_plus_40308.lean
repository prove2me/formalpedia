-- Prove2me | solution 1 for lean_workbook_plus_40308
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:50.282836+00:00
-- url     : https://prove2.me/submissions/d30209ce-0022-498c-8f1b-e481bdcf6847

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (a : ℕ → ℕ) (h₁ : ∀ n, Odd n → a n = 0) (h₂ : ∀ n, Even n → a n = n / 2) : (∀ n, (Odd n ∨ Even n) → a n = 0 ∨ a n = n / 2) := by
  intros
  exact?
