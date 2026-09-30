-- Prove2me | solution 1 for lean_workbook_plus_21729
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:34:12.016593+00:00
-- url     : https://prove2.me/submissions/78aeb944-8abb-4aa2-bd5a-69f23c04bfea

import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum

theorem solution {a b c : ℤ} (h : a + b + c = 0) :
    47 ∣ a ^ 47 + b ^ 47 + c ^ 47 := by
  have hp : Nat.Prime 47 := by decide
  have hc := ((Int.ModEq.pow_prime_eq_self hp a).add
    (Int.ModEq.pow_prime_eq_self hp b)).add (Int.ModEq.pow_prime_eq_self hp c)
  rw [h] at hc
  simpa using hc.symm.dvd

#print axioms solution
