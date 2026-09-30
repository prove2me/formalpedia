-- Prove2me | solution 1 for lean_workbook_plus_296
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:30:45.588602+00:00
-- url     : https://prove2.me/submissions/2ec78b84-cda7-4903-9729-63931258d794

import Mathlib

theorem solution : ∀ n ≥ 2, (5 ^ n + 9 < 6 ^ n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    calc
      5 ^ n * 5 + 9 < (5 ^ n + 9) * 6 := by omega
      _ < 6 ^ n * 6 := Nat.mul_lt_mul_of_pos_right ih (by decide)
