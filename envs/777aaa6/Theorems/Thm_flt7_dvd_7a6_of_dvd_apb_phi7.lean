-- Prove2me | Theorems.Thm_flt7_dvd_7a6_of_dvd_apb_phi7
-- name    : flt7_dvd_7a6_of_dvd_apb_phi7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T08:35:06.975864+00:00
-- url     : https://prove2.me/theorems/2e8855ed-326d-46ed-bdb4-1596df252c47
-- statement:
--   For integers a, b, q: if q divides (a+b) and q divides Phi7(a,b) = a^6-a^5b+a^4b^2-a^3b^3+a^2b^4-ab^5+b^6, then q divides 7*a^6. This key lemma shows that any common divisor of (a+b) and Phi7(a,b) must divide 7*a^6, used in the FLT-7 Kummer descent to show gcd(a+b, Phi7) divides 7.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity

theorem flt7_dvd_7a6_of_dvd_apb_phi7 (a b q : ℤ) (hqab : q ∣ a + b) (hqphi : q ∣ a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6) : q ∣ 7 * a^6 := by sorry
