-- Prove2me | solution 1 for fltp_phi_sq_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:09:40.005892+00:00
-- url     : https://prove2.me/submissions/e2d57a1a-55a5-4fd6-9975-29343300e134

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset in
theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    ¬(p : ℤ) ^ 2 ∣ ∑ i ∈ range p, a ^ i * (-b) ^ (p - 1 - i) := by
  have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hsub : (p : ℤ) ∣ a - (-b) := by simpa only [sub_neg_eq_add] using h_dvd
  have hval := emultiplicity_geom_sum₂_eq_one hp_int h_odd hsub h_ndvd
  exact (emultiplicity_eq_coe.mp hval).2

#print axioms solution
