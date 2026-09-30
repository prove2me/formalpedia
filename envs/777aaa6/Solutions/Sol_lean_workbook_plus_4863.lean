-- Prove2me | solution 1 for lean_workbook_plus_4863
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:21:25.480652+00:00
-- url     : https://prove2.me/submissions/9e17f687-9fa8-47bc-899f-bbecd0e0d65d

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℕ) (ha : 1 < a) : a^b ≥ a * b := by
  induction b with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h2n : 2 * n ≤ a * n := Nat.mul_le_mul_right n ha
      have hn1 : n + 1 ≤ a * n := by omega
      calc a ^ (n + 1) = a * a ^ n := by ring
        _ ≥ a * (a * n) := Nat.mul_le_mul_left a ih
        _ ≥ a * (n + 1) := Nat.mul_le_mul_left a hn1
