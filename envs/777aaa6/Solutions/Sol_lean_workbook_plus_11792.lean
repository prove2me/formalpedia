-- Prove2me | solution 1 for lean_workbook_plus_11792
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:39:11.191391+00:00
-- url     : https://prove2.me/submissions/52825d44-37a1-4871-ad03-9602dce810d4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

theorem solution : ∀ n : ℕ, 9 ∣ n^3 + (n + 1)^3 + (n + 2)^3 := by
  intro n
  apply Nat.dvd_of_mod_eq_zero
  have hn : n % 9 < 9 := Nat.mod_lt n (by decide)
  interval_cases h : n % 9 <;>
    norm_num [Nat.add_mod, Nat.pow_mod, h]

#print axioms solution
