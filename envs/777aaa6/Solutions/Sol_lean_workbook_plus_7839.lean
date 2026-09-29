-- Prove2me | solution 1 for lean_workbook_plus_7839
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T19:36:52.77948+00:00
-- url     : https://prove2.me/submissions/90896dc6-6a3c-4693-824b-a8b598e5aab9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution  (a b c a' b' c' : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x ^ 2 + b * x + c)
  (h₁ : ∀ x, g x = a' * x ^ 2 + b' * x + c')
  (h₂ : ∀ x, f x = g x) :
  a = a' ∧ b = b' ∧ c = c'   := by
  have hzero := h₂ 0
  have hone := h₂ 1
  have htwo := h₂ 2
  rw [h₀, h₁] at hzero hone htwo
  norm_num at hzero hone htwo
  constructor
  · linarith only [hzero, hone, htwo]
  constructor
  · linarith only [hzero, hone, htwo]
  · exact hzero
