-- Prove2me | solution 1 for lean_workbook_plus_67324
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:14:15.66467+00:00
-- url     : https://prove2.me/submissions/80b49b6b-8795-4092-b3b4-439475e219d1

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : n * (n + 1) / 2 = 36 ↔ n = 8 := by
  constructor
  · intro h
    have hlt : n < 9 := by
      by_contra hn
      push_neg at hn
      have : 9 * 10 ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)
      omega
    have hge : 8 ≤ n := by
      by_contra hn
      push_neg at hn
      have : n * (n + 1) ≤ 7 * 8 := Nat.mul_le_mul (by omega) (by omega)
      omega
    omega
  · rintro rfl
    norm_num
