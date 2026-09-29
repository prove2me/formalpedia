-- Prove2me | solution 1 for fltp_lte_nat
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T11:13:03.823088+00:00
-- url     : https://prove2.me/submissions/609563e4-0853-45e3-8182-4a931b7b581c

import Mathlib.NumberTheory.Multiplicity

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℕ)
    (h_odd : Odd p) (h_dvd : p ∣ a + b) (h_ndvd : ¬p ∣ a) :
    padicValNat p (a ^ p + b ^ p) = padicValNat p (a + b) + 1 := by
  rw [padicValNat.pow_add_pow h_odd h_dvd h_ndvd h_odd]
  congr 1
  exact padicValNat_self
