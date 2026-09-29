-- Prove2me | solution 1 for mme_rational_entropy_difference_log_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:59:29.186985+00:00
-- url     : https://prove2.me/submissions/4ac8d2ba-84a1-4e1b-94a5-a8f41e0a2adf

import Theorems.Thm_mme_rational_mass_entropy_log_bounds

open scoped BigOperators
open MME.RegionRate

/-- Sharp rational logarithm intervals certify entropy minus a sum of
homogeneous compatibility entropies, including zero compatibility classes. -/
theorem solution
    {W C V : Type*} [Fintype W] [Fintype C] [Fintype V]
    (p : W → ℚ) (hp : ∀ w, 0 ≤ p w)
    (x : C → V → ℚ) (hx : ∀ c v, 0 ≤ x c v)
    (pLower pUpper : W → ℚ) (xLower xUpper : C → V → ℚ)
    (hpLog : ∀ w, 0 < p w →
      (pLower w : ℝ) ≤ Real.log (p w : ℝ) ∧
        Real.log (p w : ℝ) ≤ (pUpper w : ℝ))
    (hxLog : ∀ c v, 0 < x c v / ∑ u, x c u →
      (xLower c v : ℝ) ≤ Real.log ((x c v / ∑ u, x c u : ℚ) : ℝ) ∧
        Real.log ((x c v / ∑ u, x c u : ℚ) : ℝ) ≤ (xUpper c v : ℝ))
    (bound : ℚ) :
    bound ≤ -(∑ w, p w * pUpper w) -
      ∑ c, (∑ v, x c v) * (-(∑ v, (x c v / ∑ u, x c u) * xLower c v)) →
    (bound : ℝ) ≤ entropy (fun w => (p w : ℝ)) -
      ∑ c, massEntropy (fun v => (x c v : ℝ)) := by
  intro hcert
  have hl := (mme_rational_entropy_log_bounds p hp pLower pUpper hpLog).1
  have hu := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) =>
    (mme_rational_mass_entropy_log_bounds (x c) (hx c)
      (xLower c) (xUpper c) (hxLog c)).2)
  have hc := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at hl hu hc
  linarith


#print axioms solution
