-- Prove2me | solution 1 for lean_workbook_plus_69212
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:57:43.102782+00:00
-- url     : https://prove2.me/submissions/e7896fd2-51bb-4e7d-9f8b-9c9d6854c089

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (h₁ : f 0 = 24)
    (h₂ : ∀ n, f (n + 1) = f n + 3) : ∀ n, f n = 24 + 3 * n := by
  intro n
  induction n with
  | zero => simpa using h₁
  | succ n ih => simpa [h₂, ih, Nat.mul_succ, Nat.add_assoc]

#print axioms solution
