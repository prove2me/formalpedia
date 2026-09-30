-- Prove2me | solution 1 for lean_workbook_plus_52281
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:13.427259+00:00
-- url     : https://prove2.me/submissions/168e085c-cbd9-4335-a9cd-075a48d6faeb

import Mathlib.Analysis.Complex.Basic

theorem solution (x n : ℕ) (h : ℕ → ℕ) (h₁ : ∀ x, h (x + 1) = h x + 1) : h (x + n) = h x + n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc, h₁, ih, Nat.add_assoc]
