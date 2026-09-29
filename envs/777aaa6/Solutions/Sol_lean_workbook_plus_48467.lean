-- Prove2me | solution 1 for lean_workbook_plus_48467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:18.392586+00:00
-- url     : https://prove2.me/submissions/1e237f0d-8f8a-4e67-a4c6-f093b3acc30e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c p q : ℝ)
  (h₀ : a ≠ 0)
  (h₁ : a * p^2 + b * p + c = 0)
  (h₂ : a * q^2 + b * q + c = 0)
  (h₃ : p > q)
  (h₄ : p - q = 1) :
  p + q = -b / a ∧ p * q = c / a := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
