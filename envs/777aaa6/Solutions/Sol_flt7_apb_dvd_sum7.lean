-- Prove2me | solution 1 for flt7_apb_dvd_sum7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T08:27:54.513702+00:00
-- url     : https://prove2.me/submissions/e7d04bf1-c019-4d19-8460-9e4f9e14e00c

import Mathlib.NumberTheory.Multiplicity

-- (a+b) divides (a^7+b^7) for natural numbers a, b.
-- Proof: the factorization a^7+b^7 = (a+b)*Phi7(a,b) holds in ℤ,
-- and the quotient Phi7 is a positive integer for a,b:ℕ.
theorem solution (a b : ℕ) : (a + b) ∣ (a^7 + b^7) := by
  have h : (a : ℤ) + b ∣ (a : ℤ)^7 + (b : ℤ)^7 :=
    ⟨(a : ℤ)^6 - (a : ℤ)^5*(b : ℤ) + (a : ℤ)^4*(b : ℤ)^2 -
     (a : ℤ)^3*(b : ℤ)^3 + (a : ℤ)^2*(b : ℤ)^4 - (a : ℤ)*(b : ℤ)^5 + (b : ℤ)^6,
     by ring⟩
  have h2 : ((a + b : ℕ) : ℤ) ∣ ((a^7 + b^7 : ℕ) : ℤ) := by push_cast; exact h
  exact_mod_cast h2
