-- Prove2me | Theorems.Thm_fltp_lte_nat
-- name    : fltp_lte_nat
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T11:12:48.931336+00:00
-- url     : https://prove2.me/theorems/0e7b9c96-99b3-4b7a-8c32-68fe6830b9b9
-- statement:
--   Lifting the Exponent Lemma for natural numbers: If p is an odd prime, p divides a+b, and p does not divide a, then padicValNat p (a^p + b^p) = padicValNat p (a+b) + 1.
-- source:
--   https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma

import Mathlib.NumberTheory.Multiplicity

theorem fltp_lte_nat (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℕ)
    (h_odd : Odd p) (h_dvd : p ∣ a + b) (h_ndvd : ¬p ∣ a) :
    padicValNat p (a ^ p + b ^ p) = padicValNat p (a + b) + 1 := by sorry
