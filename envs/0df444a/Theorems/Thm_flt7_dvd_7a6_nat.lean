-- Prove2me | Theorems.Thm_flt7_dvd_7a6_nat
-- name    : flt7_dvd_7a6_nat
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T08:51:11.689174+00:00
-- url     : https://prove2.me/theorems/1ccfa8cc-6e41-4cd5-8f04-81ed1e631086
-- statement:
--   For natural numbers a, b, q with a+b ≠ 0: if q divides (a+b) and q divides the natural number quotient (a^7+b^7)/(a+b), then q divides 7*a^6. This ℕ version bridges the gap between the integer Phi7 polynomial and the natural number arithmetic, used to prove that gcd(a+b, Phi7_nat) divides 7 in the FLT-7 Kummer descent.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity

theorem flt7_dvd_7a6_nat (a b q : ℕ) (hab_ne : a+b ≠ 0) (hqab : q ∣ a+b) (hqphi : q ∣ (a^7+b^7)/(a+b)) : q ∣ 7*a^6 := by sorry
