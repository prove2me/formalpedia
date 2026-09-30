-- Prove2me | solution 1 for lean_workbook_plus_37106
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:39.39606+00:00
-- url     : https://prove2.me/submissions/7c50e6db-fd74-4932-afdc-639ffa327223

import Mathlib

set_option autoImplicit false

theorem solution (x a b c d : ℕ) (hx : x = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    x = 1 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have hprod := hx.symm.trans h
    have hd := Nat.eq_one_of_mul_eq_one_left hprod
    have habc := Nat.eq_one_of_mul_eq_one_right hprod
    have hc := Nat.eq_one_of_mul_eq_one_left habc
    have hab := Nat.eq_one_of_mul_eq_one_right habc
    have hb := Nat.eq_one_of_mul_eq_one_left hab
    have ha := Nat.eq_one_of_mul_eq_one_right hab
    exact ⟨by simpa using ha, by simpa using hb, by simpa using hc, by simpa using hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simpa using hx

#print axioms solution
