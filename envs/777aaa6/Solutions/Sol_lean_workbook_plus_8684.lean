-- Prove2me | solution 1 for lean_workbook_plus_8684
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:23:57.077614+00:00
-- url     : https://prove2.me/submissions/bff1d5bb-9723-442c-8168-f74bd42311dc

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : ∑' n : ℕ, (n / 3 ^ n) = 3 / 4 := by
  have h : ∀ n : ℕ, n / 3 ^ n = 0 := fun n =>
    Nat.div_eq_of_lt (Nat.lt_pow_self (by norm_num))
  simp [h]
