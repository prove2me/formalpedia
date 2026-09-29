-- Prove2me | solution 1 for lean_workbook_plus_57421
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:33.641486+00:00
-- url     : https://prove2.me/submissions/cf5e1f36-b7a2-42c2-b7d9-a2a48a388525

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c α β γ : ℝ) (h₁ : α = b * c - a ^ 2) (h₂ : β = c * a - b ^ 2) (h₃ : γ = a * b - c ^ 2) : a * α + b * β + c * γ = (a + b + c) * (α + β + γ) := by
  intros
  grind
