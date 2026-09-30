-- Prove2me | solution 1 for lean_workbook_plus_71643
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:32:24.564345+00:00
-- url     : https://prove2.me/submissions/a277f250-4ef8-4163-9561-6813bc89be70

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

theorem solution (a : ℕ) : 3 ∣ (a-2)*(a-1)*a ∧ 3 ∣ a*(a+1)*(a+2) := by
  have consecutive (n : ℕ) : 3 ∣ n * (n + 1) * (n + 2) := by
    apply Nat.dvd_of_mod_eq_zero
    have hn : n % 3 < 3 := Nat.mod_lt n (by decide)
    interval_cases h : n % 3 <;>
      norm_num [Nat.mul_mod, Nat.add_mod, h]
  constructor
  · by_cases ha : a < 2
    · interval_cases a <;> norm_num
    · have h1 : a - 2 + 1 = a - 1 := by omega
      have h2 : a - 2 + 2 = a := by omega
      simpa [h1, h2] using consecutive (a - 2)
  · exact consecutive a

#print axioms solution
