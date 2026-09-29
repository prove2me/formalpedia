-- Prove2me | solution 1 for lean_workbook_plus_57584
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:29.072146+00:00
-- url     : https://prove2.me/submissions/497a5423-ebf9-4757-ad1f-9cd1294c315a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x a b c : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : a < b ∧ b < c)
  (h₂ : a + b + c = 6)
  (h₃ : b = 2 * a)
  (h₄ : c = 2 * a + 0.5 + x) :
  a = 1.1 - x / 5 ∧ b = 2.2 - 2 * x / 5 ∧ c = 2.7 + 3 * x / 5 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
