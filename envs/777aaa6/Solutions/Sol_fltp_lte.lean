-- Prove2me | solution 1 for fltp_lte
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T10:51:20.001753+00:00
-- url     : https://prove2.me/submissions/95a98836-1f3c-45f2-b4ec-79669703d4b0

import Mathlib.NumberTheory.Multiplicity

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    emultiplicity (p : ℤ) (a ^ p + b ^ p) =
    emultiplicity (p : ℤ) (a + b) + 1 := by
  have hprime : Nat.Prime p := hp.out
  have lte := Int.emultiplicity_pow_add_pow hprime h_odd h_dvd h_ndvd h_odd
  rw [lte]
  congr 1
  exact hprime.emultiplicity_self
