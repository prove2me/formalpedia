-- Prove2me | solution 1 for lean_workbook_plus_61342
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:56:18.712192+00:00
-- url     : https://prove2.me/submissions/7ecdfcdf-3f8f-4ed7-9c33-dc63346e9eec

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.ModEq

theorem solution
    (h : ∀ p : ℕ, Nat.Prime p → ¬ 9 ∣ (p ^ 2016 - 2017)) : False := by
  apply h 2 (by decide)
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  have h6 : Nat.ModEq 9 (2 ^ 6) 1 := by decide
  have hp := h6.pow 336
  simpa only [← pow_mul, show (6 : ℕ) * 336 = 2016 from rfl, one_pow] using hp

#print axioms solution
