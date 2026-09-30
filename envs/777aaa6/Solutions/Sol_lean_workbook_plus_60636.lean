-- Prove2me | solution 1 for lean_workbook_plus_60636
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:18:43.303967+00:00
-- url     : https://prove2.me/submissions/360767de-40c1-491a-975e-1002f4cf133a

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℕ → ℝ) (hab : ∀ n, a n ≤ b n) (h1 : ∀ n, [a n, b n] ⊆ [a (n + 1), b (n + 1)]): ∃ x, ∀ n, x ∈ [a n, b n] := by
  refine ⟨a 0, ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ k ih => exact h1 k ih
