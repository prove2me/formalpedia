-- Prove2me | solution 1 for lean_workbook_plus_63318
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:38.976899+00:00
-- url     : https://prove2.me/submissions/cbd30336-9d71-4f23-9302-6311b56fd4de

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

theorem solution (n : ℕ) : 6 ∣ (n + 1) * (n + 2) * (n + 3) := by
  apply Nat.dvd_of_mod_eq_zero
  have h : n % 6 < 6 := Nat.mod_lt n (by norm_num)
  interval_cases he : n % 6 <;> norm_num [Nat.mul_mod, Nat.add_mod, he]
