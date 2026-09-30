-- Prove2me | solution 1 for lean_workbook_plus_64367
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:30.025072+00:00
-- url     : https://prove2.me/submissions/82cbaa3b-bc75-4e1b-8309-5053b38b45f4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (f : ℝ → ℝ)
    (h₁ : ∀ x, f x ≤ x)
    (h₂ : ∀ x y, f (x + y) ≤ f x + f y) :
    ∀ x, f x = x := by
  have hz := h₂ 0 0
  rw [zero_add] at hz
  have hzero : f 0 = 0 := by linarith [h₁ 0]
  intro x
  have hx := h₂ x (-x)
  rw [add_neg_cancel, hzero] at hx
  linarith [h₁ x, h₁ (-x)]
