-- Prove2me | solution 1 for lean_workbook_plus_10087
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:40:08.034577+00:00
-- url     : https://prove2.me/submissions/e903d3fb-1dc8-4dda-a441-e471aac1f924

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (hf: f 0 = 1) (hf2 : ∀ n, f (n + 1) = f n - 1) : ∀ n, f n = 1 - n := by
  intro n
  induction n with
  | zero => simpa using hf
  | succ k ih => rw [hf2, ih]; omega
