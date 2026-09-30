-- Prove2me | solution 1 for lean_workbook_plus_69515
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:49.596899+00:00
-- url     : https://prove2.me/submissions/1f438957-31b6-45c1-bb55-5e724f1c1ddd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (f : ℕ → ℝ) (n : ℕ) (h₁ : f 1 = 1 / 2)
    (h₂ : ∀ x y : ℕ, f (x + y) = f x * f y) :
    f n = (1 / 2)^n := by
  have hz : f 0 = 1 := by
    have h01 := h₂ 0 1
    rw [zero_add, h₁] at h01
    linarith
  induction n with
  | zero => simpa using hz
  | succ n ih => rw [h₂ n 1, h₁, ih, pow_succ]
