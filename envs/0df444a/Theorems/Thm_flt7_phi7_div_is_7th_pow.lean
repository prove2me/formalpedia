-- Prove2me | Theorems.Thm_flt7_phi7_div_is_7th_pow
-- name    : flt7_phi7_div_is_7th_pow
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T09:35:41.065575+00:00
-- url     : https://prove2.me/theorems/f242e58c-6c3b-44c0-a194-e6729dad6232
-- statement:
--   In the FLT-7 Kummer descent setting (a^7+b^7=c^7, gcd(a,b)=1, 7|a+b, c=7*c1 with 7 not dividing c1 or a), the reduced cyclotomic quotient (a^7+b^7)/(a+b)/7 is a perfect 7th power. This is the symmetric counterpart to flt7_apb_div_is_7th_pow: both factors of the descent equation A*B=c1^7 are 7th powers, since gcd(A,B)=1. Applying Int.eq_pow_of_mul_eq_pow_odd_left to the B*A factorization gives the result.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas

theorem flt7_phi7_div_is_7th_pow (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c) (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) (hcop : Nat.Coprime a b) : ∃ e : ℕ, (a^7+b^7)/(a+b) / 7 = e^7 := by sorry
