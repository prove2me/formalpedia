-- Prove2me | solution 1 for mme_rational_log_series_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:51:47.294983+00:00
-- url     : https://prove2.me/submissions/1210d950-7fd1-4e72-9c53-7671ac1b16ac

import Theorems.Thm_mme_dyadic_log_series_bounds

open scoped BigOperators

/-- Two finite rational inequalities certify an enclosure of a rational
argument's real logarithm, with the series remainder included. -/
theorem solution
    (q : ℚ) (hq : 0 < q) (k : ℤ) (n : ℕ) (lower upper : ℚ) :
    let t := ((2 : ℚ) ^ k * q - 1) / ((2 : ℚ) ^ k * q + 1)
    let twoCenter := 2 * ∑ i ∈ Finset.range n, (1 / 3 : ℚ) ^ (2 * i + 1) / (2 * i + 1)
    let twoError := 2 * ((1 / 3 : ℚ) ^ (2 * n + 1) / (1 - (1 / 3 : ℚ) ^ 2))
    let center := (2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1)) -
      (k : ℚ) * twoCenter
    let error := 2 * (|t| ^ (2 * n + 1) / (1 - t ^ 2)) + |(k : ℚ)| * twoError
    lower ≤ center - error → center + error ≤ upper →
      (lower : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (upper : ℝ) := by
  intro t twoCenter twoError center error hl hu
  have h := mme_dyadic_log_series_bounds (q : ℝ) (by exact_mod_cast hq) k n
  have hlR := (Rat.cast_le (K := ℝ)).2 hl
  have huR := (Rat.cast_le (K := ℝ)).2 hu
  dsimp only [center, error, t, twoCenter, twoError] at hlR huR
  push_cast at hlR huR
  exact ⟨hlR.trans h.1, h.2.trans huR⟩


#print axioms solution
