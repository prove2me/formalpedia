-- Prove2me | Theorems.Thm_fltp_case2_val_bound
-- name    : fltp_case2_val_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T11:20:43.012222+00:00
-- url     : https://prove2.me/theorems/006f91be-b6fc-4e19-8dac-88e718d1861b
-- statement:
--   In FLT Case 2 (p | c, p ∤ a, p ∤ b, a^p + b^p = c^p): the p-adic valuation satisfies p * padicValNat p c = padicValNat p (a+b) + 1. This follows from LTE (padicValNat p (a^p+b^p) = padicValNat p (a+b) + 1) and padicValNat(c^p) = p * padicValNat(c).
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

theorem fltp_case2_val_bound (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c : ℕ)
    (h_odd : Odd p) (heq : a ^ p + b ^ p = c ^ p)
    (hc : c ≠ 0) (h_ndvd_a : ¬p ∣ a) (h_dvd_c : p ∣ c) :
    p * padicValNat p c = padicValNat p (a + b) + 1 := by sorry
