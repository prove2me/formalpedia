-- Prove2me | solution 1 for lean_workbook_plus_60103
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:34.094459+00:00
-- url     : https://prove2.me/submissions/0ac6db2b-09c3-4204-8b5e-e3ff34312061

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) (f : ℝ → ℝ)
    (h₁ : a ≠ -b)
    (h₂ : ∀ x, a * f x + b * f (1 - x) = x) :
    ∀ x, f x + f (1 - x) = 1 / (a + b) := by
  have hab : a + b ≠ 0 := by
    intro h
    apply h₁
    linarith
  intro x
  have hx := h₂ x
  have hr := h₂ (1 - x)
  have harg : 1 - (1 - x) = x := by linarith
  rw [harg] at hr
  apply (eq_div_iff hab).2
  nlinarith
