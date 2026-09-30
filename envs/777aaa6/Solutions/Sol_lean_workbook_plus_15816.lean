-- Prove2me | solution 1 for lean_workbook_plus_15816
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:47:46.303376+00:00
-- url     : https://prove2.me/submissions/995bfb51-dea8-41b2-9f4e-4f42fad25e5f

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (n : ℕ) (h₁ : ∀ x, f x = f (x + 1) + 1): ∀ x, f (x + n) = f x - n := by
  intro x
  induction n with
  | zero => simp
  | succ k ih =>
    have h := h₁ (x + k)
    push_cast
    rw [← add_assoc]
    linarith [h, ih]
