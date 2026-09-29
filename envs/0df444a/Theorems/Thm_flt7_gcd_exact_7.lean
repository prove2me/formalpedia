-- Prove2me | Theorems.Thm_flt7_gcd_exact_7
-- name    : flt7_gcd_exact_7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T08:56:31.282047+00:00
-- url     : https://prove2.me/theorems/e7bfa8c6-624f-4857-8a35-6b61b9d2fffe
-- statement:
--   For coprime positive naturals a, b with a^7+b^7=c^7 and c=7*c1 (7 not dividing a or c1, 7 dividing a+b): the gcd of (a+b) and the natural quotient (a^7+b^7)/(a+b) equals exactly 7. This combines the upper bound (gcd divides 7, from coprimality) and the lower bound (7 divides gcd, from the Lifting the Exponent Lemma). Key lemma in the FLT-7 Kummer descent.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt7_gcd_exact_7 (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c) (h_eq : a ^ 7 + b ^ 7 = c ^ 7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b) (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) (hcop : Nat.Coprime a b) : Nat.gcd (a+b) ((a^7+b^7)/(a+b)) = 7 := by sorry
