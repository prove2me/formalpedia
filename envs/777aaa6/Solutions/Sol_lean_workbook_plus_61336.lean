-- Prove2me | solution 1 for lean_workbook_plus_61336
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:30.726027+00:00
-- url     : https://prove2.me/submissions/caf8f9ea-e0f4-4ac8-8207-aaad55536bdc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (habc : a * b * c ≠ 0) :
    (∃ x y : ℤ, a * x + b * y = c) ↔ (gcd a b) ∣ c := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left a b) x)
      (dvd_mul_of_dvd_left (gcd_dvd_right a b) y)
  · rintro ⟨k, hk⟩
    refine ⟨Int.gcdA a b * k, Int.gcdB a b * k, ?_⟩
    calc
      a * (Int.gcdA a b * k) + b * (Int.gcdB a b * k) =
          (a * Int.gcdA a b + b * Int.gcdB a b) * k := by ring
      _ = gcd a b * k := by rw [← Int.gcd_eq_gcd_ab, Int.coe_gcd]
      _ = c := hk.symm

#print axioms solution
