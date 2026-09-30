-- Prove2me | solution 1 for lean_workbook_plus_17553
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:19.525766+00:00
-- url     : https://prove2.me/submissions/d173b7b4-eda5-43dd-b935-872ac70db6df

import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

theorem solution (p : ℕ) (hp : p.Prime) : p ^ 2 ∣ 2 ^ (p + 1) → p = 2 := by
  intro h
  have hpow : p ∣ 2 ^ (p + 1) :=
    Nat.dvd_trans ⟨p, by simp only [pow_two]⟩ h
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpow)

#print axioms solution
