-- Prove2me | solution 1 for mme_rational_entropy_difference_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:15.503711+00:00
-- url     : https://prove2.me/submissions/01c393a5-980e-446c-ae89-d57782217dd0

import Theorems.Thm_mme_mass_entropy_dyadic_upper

open scoped BigOperators
open MME.RegionRate

/-- A rational certificate bounds an entropy minus a sum of homogeneous
entropies. Zero compatibility classes are allowed. -/
theorem solution
    {W C V : Type*} [Fintype W] [Fintype C] [Fintype V]
    (p : W → ℚ) (hp : ∀ w, 0 ≤ p w)
    (x : C → V → ℚ) (hx : ∀ c v, 0 ≤ x c v)
    (kp : W → ℕ) (kx : C → V → ℕ) (b : ℚ) :
    b ≤
      (∑ w, p w * ((kp w : ℚ) * (693147180 / 1000000000) + 1 -
        2 ^ kp w * p w)) -
      ∑ c, (∑ v, x c v) * ∑ v, (x c v / ∑ u, x c u) *
        ((kx c v : ℚ) * (693147181 / 1000000000) - 1 +
          (2 ^ kx c v * (x c v / ∑ u, x c u))⁻¹) →
    (b : ℝ) ≤ entropy (fun w => (p w : ℝ)) -
      ∑ c, massEntropy (fun v => (x c v : ℝ)) := by
  intro hcert
  have hpR (w : W) : (0 : ℝ) ≤ p w := by exact_mod_cast hp w
  have hxR (c : C) (v : V) : (0 : ℝ) ≤ x c v := by exact_mod_cast hx c v
  have hl := (mme_entropy_dyadic_bounds (fun w => (p w : ℝ)) hpR kp).1
  have hu := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) =>
    mme_mass_entropy_dyadic_upper (fun v => (x c v : ℝ)) (hxR c) (kx c))
  have hcertR := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at hcertR
  linarith


#print axioms solution
