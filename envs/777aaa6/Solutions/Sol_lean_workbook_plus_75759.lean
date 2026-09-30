-- Prove2me | solution 1 for lean_workbook_plus_75759
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:43:40.983305+00:00
-- url     : https://prove2.me/submissions/5313d643-24bd-40da-b119-3960f66b3f36

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : 0 < n) : (n + 1) ≤ ((n + 1) / n)^n * (n + 2) := by
  have h1 : 1 ≤ (n + 1) / n := by
    rw [Nat.le_div_iff_mul_le hn]
    omega
  have h2 : 1 ≤ ((n + 1) / n)^n := Nat.one_le_pow _ _ h1
  calc n + 1 ≤ n + 2 := by omega
    _ = 1 * (n + 2) := by ring
    _ ≤ ((n + 1) / n)^n * (n + 2) := Nat.mul_le_mul_right _ h2
