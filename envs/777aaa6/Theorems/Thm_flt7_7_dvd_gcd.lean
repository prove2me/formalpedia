-- Prove2me | Theorems.Thm_flt7_7_dvd_gcd
-- name    : flt7_7_dvd_gcd
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T08:30:56.75054+00:00
-- url     : https://prove2.me/theorems/798f70ef-0bbf-483a-90bb-b7e21c12f358
-- statement:
--   In the FLT-7 setting, 7 divides gcd(a+b, Phi7_nat) where Phi7_nat = (a^7+b^7)/(a+b). This follows from 7 dividing a+b (given) and the 7-adic valuation of Phi7_nat being 1 (hence 7 divides Phi7_nat). Together these imply 7 divides both arguments of the gcd.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt7_7_dvd_gcd (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c) (h_eq : a ^ 7 + b ^ 7 = c ^ 7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b) (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) : 7 ∣ Nat.gcd (a + b) ((a^7 + b^7) / (a + b)) := by sorry
