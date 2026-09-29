-- Prove2me | Theorems.Thm_fltp_apb_val_eq_pm1
-- name    : fltp_apb_val_eq_pm1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T09:56:10.208937+00:00
-- url     : https://prove2.me/theorems/c7448103-3747-4ffb-ada4-d07d15e27c9b
-- statement:
--   For any odd prime p, if a^p+b^p=c^p with c=p*c1 (p not dividing a or c1) and p dividing a+b, then the p-adic valuation of (a+b) is exactly p-1. This is the general version of flt7_apb_val_eq_6 (p=7 gives p-1=6). Proof: the Lifting the Exponent Lemma gives v_p(a^p+b^p) = v_p(a+b)+1; the right side satisfies v_p(c^p) = p*v_p(c) = p*(v_p(p)+v_p(c1)) = p*1 = p. So v_p(a+b)+1 = p, giving v_p(a+b) = p-1.
-- source:
--   https://en.wikipedia.org/wiki/Lifting_the_exponent_lemma

import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.Basic

theorem fltp_apb_val_eq_pm1 (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c c1 : ℕ) (ha : 0 < a) (hc_pos : 0 < c) (h_eq : a^p + b^p = c^p) (h_odd : Odd p) (hpa : ¬p ∣ a) (hpab : p ∣ a+b) (hc : c = p*c1) (hpc1 : ¬p ∣ c1) : padicValNat p (a+b) = p - 1 := by sorry
