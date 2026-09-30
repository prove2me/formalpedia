-- Prove2me | solution 1 for lean_workbook_plus_69273
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:10.24929+00:00
-- url     : https://prove2.me/submissions/adcbd3d0-5ad9-4c09-a650-736fb7b0f0ca

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.ModEq

theorem solution (a m b n : ℕ) (h₀ : 0 < n) (h₁ : 0 < a)
    (h₂ : 0 < b) (h₃ : b < a) : a ∣ (a*m + b)^n - b^n := by
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

#print axioms solution
