-- Prove2me | solution 1 for mme_dyadic_log_series_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T11:44:57.397989+00:00
-- url     : https://prove2.me/submissions/6f8b3a84-86ff-42be-be45-8ec1332742e7

import Theorems.Thm_mme_log_series_bounds

open scoped BigOperators

/-- Integer dyadic scaling gives a rapidly convergent logarithm enclosure for
both small probabilities and large dual weights, using rational arithmetic. -/
theorem solution (x : ℝ) (hx : 0 < x) (k : ℤ) (n : ℕ) :
    let t := ((2 : ℝ) ^ k * x - 1) / ((2 : ℝ) ^ k * x + 1)
    let twoCenter := 2 * ∑ i ∈ Finset.range n, (1 / 3 : ℝ) ^ (2 * i + 1) / (2 * i + 1)
    let twoError := 2 * ((1 / 3 : ℝ) ^ (2 * n + 1) / (1 - (1 / 3 : ℝ) ^ 2))
    let center := (2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1)) -
      (k : ℝ) * twoCenter
    let error := 2 * (|t| ^ (2 * n + 1) / (1 - t ^ 2)) + |(k : ℝ)| * twoError
    center - error ≤ Real.log x ∧ Real.log x ≤ center + error := by
  intro t twoCenter twoError center error
  have hspos : 0 < (2 : ℝ) ^ k * x := mul_pos (zpow_pos (by norm_num) _) hx
  have hs := mme_log_series_bounds ((2 : ℝ) ^ k * x) hspos n
  have htwo : twoCenter - twoError ≤ Real.log 2 ∧
      Real.log 2 ≤ twoCenter + twoError := by
    simpa only [show ((2 : ℝ) - 1) / (2 + 1) = 1 / 3 by norm_num,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 3)] using
      mme_log_series_bounds 2 (by norm_num) n
  have hlog : Real.log ((2 : ℝ) ^ k * x) = (k : ℝ) * Real.log 2 + Real.log x := by
    rw [Real.log_mul (ne_of_gt (zpow_pos (by norm_num) _)) hx.ne', Real.log_zpow]
  have ha : |Real.log 2 - twoCenter| ≤ twoError := abs_le.mpr (by
    constructor <;> linarith [htwo.1, htwo.2])
  have hb : |Real.log ((2 : ℝ) ^ k * x) -
      (2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1))| ≤
      2 * (|t| ^ (2 * n + 1) / (1 - t ^ 2)) := abs_le.mpr (by
    constructor <;> linarith [hs.1, hs.2])
  have hc : |Real.log x - center| ≤ error := by
    rw [show Real.log x - center =
      (Real.log ((2 : ℝ) ^ k * x) -
        (2 * ∑ i ∈ Finset.range n, t ^ (2 * i + 1) / (2 * i + 1))) -
          (k : ℝ) * (Real.log 2 - twoCenter) by
        rw [hlog]
        dsimp only [center]
        ring]
    exact (abs_sub _ _).trans (add_le_add hb (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ha (abs_nonneg _)))
  have h := abs_le.mp hc
  constructor <;> linarith [h.1, h.2]


#print axioms solution
