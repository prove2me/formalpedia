-- Prove2me | solution 1 for lean_workbook_plus_72940
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:43:17.699357+00:00
-- url     : https://prove2.me/submissions/af68f47b-cb58-4759-b236-624d5d261bae

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (D n : ℤ) (hn : D = -3 * n^2 + 6 * n + 1)
    (hD : D >= 0) : n = 0 ∨ n = 1 ∨ n = 2 := by
  rw [hn] at hD
  by_contra h
  have hc : n ≤ -1 ∨ 3 ≤ n := by omega
  rcases hc with hlow | hhigh
  · nlinarith [sq_nonneg n]
  · nlinarith [sq_nonneg (n - 3)]

#print axioms solution
