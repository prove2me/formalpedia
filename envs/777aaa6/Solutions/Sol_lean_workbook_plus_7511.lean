-- Prove2me | solution 1 for lean_workbook_plus_7511
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:30.143207+00:00
-- url     : https://prove2.me/submissions/073470e6-d90b-492d-90bc-157aa30bf8b4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {α β : ℝ} (hab : α ≠ β) (hα : α^2 - α - 1 = 0)  (hβ : β^2 - β - 1 = 0) (a : ℕ → ℝ) (h : ∀ n, a n = (α^n - β^n) / (α - β)) : ∀ n, a (n + 2) = a (n + 1) + a n := by
  intros
  grind
