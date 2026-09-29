-- Prove2me | solution 1 for fltp_emult_phi_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-15T11:10:17.092445+00:00
-- url     : https://prove2.me/submissions/590789fa-cc66-4e19-ae50-23a76492ec8e

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    emultiplicity (p : ℤ) (∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i)) = 1 := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hxy : (p : ℤ) ∣ a - (-b) := by rwa [sub_neg_eq_add]
  exact emultiplicity_geom_sum₂_eq_one hp' h_odd hxy h_ndvd
