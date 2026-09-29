-- Prove2me | solution 1 for lean_workbook_plus_43402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:33:02.864796+00:00
-- url     : https://prove2.me/submissions/e015c9b3-9277-4326-8b58-a9f01e7dfa90

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b + c = 1)
  (h₂ : a / b = b / c)
  (h₃ : b / c = c / a) :
  a / b = 1 ∧ b / c = 1 ∧ c / a = 1 := by
  intros
  grind
