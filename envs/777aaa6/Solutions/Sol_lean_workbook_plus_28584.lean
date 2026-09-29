-- Prove2me | solution 1 for lean_workbook_plus_28584
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T19:36:53.523022+00:00
-- url     : https://prove2.me/submissions/e536d69f-cc21-4fa4-b27a-4fc340fdfda6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (g : ℝ → ℝ) (h : ∀ x, g (x^2) = -g x) : g 0 = 0 ∧ g 1 = 0 ∧ ∀ x, g (-x) = g x   := by
  have hzero := h 0
  have hone := h 1
  norm_num at hzero hone
  refine ⟨by linarith only [hzero], by linarith only [hone], ?_⟩
  intro x
  have hneg := h (-x)
  rw [neg_sq] at hneg
  linarith only [hneg, h x]
