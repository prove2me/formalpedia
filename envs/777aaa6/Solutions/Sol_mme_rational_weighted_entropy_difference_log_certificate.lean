-- Prove2me | solution 1 for mme_rational_weighted_entropy_difference_log_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:59:30.289085+00:00
-- url     : https://prove2.me/submissions/5b27b740-e225-4b32-98f3-e74f53258cca

import Theorems.Thm_mme_rational_mass_entropy_log_bounds

open scoped BigOperators
open MME.RegionRate

/-- Certified logarithms bound a weighted sum of parent entropies minus
homogeneous compatibility entropies. The weights and profiles are rational. -/
theorem solution
    {A W C V : Type*} [Fintype A] [Fintype W] [Fintype C] [Fintype V]
    (weight : A → ℚ) (hweight : ∀ a, 0 ≤ weight a)
    (p : A → W → ℚ) (hp : ∀ a w, 0 ≤ p a w)
    (x : C → V → ℚ) (hx : ∀ c v, 0 ≤ x c v)
    (pLower pUpper : A → W → ℚ) (xLower xUpper : C → V → ℚ)
    (hpLog : ∀ a w, 0 < p a w →
      (pLower a w : ℝ) ≤ Real.log (p a w : ℝ) ∧
        Real.log (p a w : ℝ) ≤ (pUpper a w : ℝ))
    (hxLog : ∀ c v, 0 < x c v / ∑ u, x c u →
      (xLower c v : ℝ) ≤ Real.log ((x c v / ∑ u, x c u : ℚ) : ℝ) ∧
        Real.log ((x c v / ∑ u, x c u : ℚ) : ℝ) ≤ (xUpper c v : ℝ))
    (bound : ℚ) :
    bound ≤ (∑ a, weight a * (-(∑ w, p a w * pUpper a w))) -
      ∑ c, (∑ v, x c v) * (-(∑ v, (x c v / ∑ u, x c u) * xLower c v)) →
    (bound : ℝ) ≤ (∑ a, (weight a : ℝ) * entropy (fun w => (p a w : ℝ))) -
      ∑ c, massEntropy (fun v => (x c v : ℝ)) := by
  intro hcert
  have hwR (a : A) : (0 : ℝ) ≤ weight a := by exact_mod_cast hweight a
  have hl := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (mme_rational_entropy_log_bounds (p a) (hp a)
        (pLower a) (pUpper a) (hpLog a)).1 (hwR a))
  have hu := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) =>
    (mme_rational_mass_entropy_log_bounds (x c) (hx c)
      (xLower c) (xUpper c) (hxLog c)).2)
  have hc := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at hl hu hc
  linarith


#print axioms solution
