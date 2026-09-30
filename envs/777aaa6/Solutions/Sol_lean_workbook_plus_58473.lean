-- Prove2me | solution 1 for lean_workbook_plus_58473
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:02:42.641728+00:00
-- url     : https://prove2.me/submissions/acf2ae0d-b99d-417f-818f-b8cecb791bfc

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (x n : ℕ) (h₁ : ∀ x, f (x + 1) = f x + 1) (h₂ : f n = n) : f (x + n) = f x + n := by
  clear h₂
  induction n with
  | zero => simp
  | succ m ih => rw [← add_assoc, h₁, ih]; ring
