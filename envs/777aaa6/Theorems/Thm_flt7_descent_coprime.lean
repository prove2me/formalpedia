-- Prove2me | Theorems.Thm_flt7_descent_coprime
-- name    : flt7_descent_coprime
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T09:12:21.72108+00:00
-- url     : https://prove2.me/theorems/8f59799c-d023-44f7-bc06-3885de70da04
-- statement:
--   In the FLT-7 Kummer descent setting: the components (a+b)/7^6 and (a^7+b^7)/(a+b)/7 are coprime. This follows from gcd(a+b, Phi7_nat) = 7: any common divisor g of the two components also divides a+b and Phi7_nat (after scaling by 7^6 and 7), so g | gcd = 7. Since 7 does not divide (a+b)/7^6 (which has padicValNat 0), g cannot equal 7, so g = 1.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt7_descent_coprime (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c) (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) (hcop : Nat.Coprime a b) : Nat.Coprime ((a+b) / 7^6) ((a^7+b^7)/(a+b) / 7) := by sorry
