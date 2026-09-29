-- Prove2me | Theorems.Thm_flt7_descent_equation
-- name    : flt7_descent_equation
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T09:05:38.488018+00:00
-- url     : https://prove2.me/theorems/a20ce1d2-2056-4a4f-b3a7-bd76c9f81f72
-- statement:
--   The key Kummer descent equation for FLT-7: if a^7+b^7=c^7 with c=7*c1 (7 not dividing a or c1, 7 dividing a+b), then ((a+b)/7^6) * ((a^7+b^7)/(a+b)/7) = c1^7. Since v_7(a+b)=6 and v_7(Phi7)=1, the 7-removed components multiply to c1^7. Combined with coprimality of the components (gcd((a+b)/7^6, Phi7/7)=1), this forces each to be a perfect 7th power, giving the descent.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem flt7_descent_equation (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c) (h_eq : a^7+b^7 = c^7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a+b) (hc : c = 7*c1) (h7c1 : ¬7 ∣ c1) : ((a+b) / 7^6) * ((a^7+b^7)/(a+b) / 7) = c1^7 := by sorry
