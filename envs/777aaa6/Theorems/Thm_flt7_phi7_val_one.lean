-- Prove2me | Theorems.Thm_flt7_phi7_val_one
-- name    : flt7_phi7_val_one
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T08:27:45.345208+00:00
-- url     : https://prove2.me/theorems/adf6aaf2-68d6-46a2-a6f9-5b6b75ce1cc2
-- statement:
--   In the FLT-7 setting (a^7+b^7=c^7, c=7c1 with 7 not dividing c1, 7 not dividing a, 7 divides a+b), the 7-adic valuation of Phi_7(a,b) = (a^7+b^7)/(a+b) equals 1. This follows from: v_7(a^7+b^7)=7, v_7(a+b)=6 (by LTE), and multiplicativity of the 7-adic valuation.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.Data.Nat.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

theorem flt7_phi7_val_one (a b c c1 : ℕ) (ha : 0 < a) (hb : 0 < b) (hc_pos : 0 < c) (h_eq : a ^ 7 + b ^ 7 = c ^ 7) (h7a : ¬7 ∣ a) (h7ab : 7 ∣ a + b) (hc : c = 7 * c1) (h7c1 : ¬7 ∣ c1) : padicValNat 7 ((a^7 + b^7) / (a + b)) = 1 := by sorry
