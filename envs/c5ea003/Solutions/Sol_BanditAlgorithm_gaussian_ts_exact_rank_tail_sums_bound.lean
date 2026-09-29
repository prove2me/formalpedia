-- Prove2me | solution 1 for BanditAlgorithm.gaussian_ts_exact_rank_tail_sums_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T23:00:23.987707+00:00
-- url     : https://prove2.me/submissions/3f10f6a4-2f63-404b-ba1f-a7478c80e6f2

import Theorems.Thm_BanditAlgorithm_gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_bound
import Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_exact_rank_large_tail_sum_bound

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

private theorem log_nat_nonneg_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ Real.log n := by
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        IsGaussianTSPolicy π →
        ∀ (i₀ : Fin k),
          banditArmMean (gaussianBandit μvec) i₀ =
            banditOptimalMean (gaussianBandit μvec) →
        ∀ (i : Fin k), 0 < banditGap (gaussianBandit μvec) i →
        ∀ n : ℕ, 2 ≤ n →
          1 + (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
                ENNReal.ofReal
                  (1 / gaussianTSTailProb i₀ s
                    (banditArmMean (gaussianBandit μvec) i₀ -
                      banditGap (gaussianBandit μvec) i / 2) h - 1)
                ∂banditMeasure (gaussianBandit μvec) π n)
            + ∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
                (if 1 / (n : ℝ) <
                    gaussianTSTailProb i s
                      (banditArmMean (gaussianBandit μvec) i₀ -
                        banditGap (gaussianBandit μvec) i / 2) h
                  then (1 : ℝ≥0∞) else 0)
                ∂banditMeasure (gaussianBandit μvec) π n ≤
            ENNReal.ofReal
              (C * (1 + Real.log n /
                banditGap (gaussianBandit μvec) i ^ 2)) := by
  obtain ⟨C₀, hC₀, hopt⟩ :=
    gaussian_ts_optimal_exact_rank_reciprocal_tail_sum_bound
  obtain ⟨Cᵢ, hCᵢ, hsub⟩ :=
    gaussian_ts_suboptimal_exact_rank_large_tail_sum_bound
  refine ⟨1 + 4 * C₀ + Cᵢ, by positivity, ?_⟩
  intro k _ μvec π hπ i₀ hi₀ i hi n hn
  have hε : 0 < banditGap (gaussianBandit μvec) i / 2 := by positivity
  have hA := hopt k μvec π i₀ hi₀
    (banditGap (gaussianBandit μvec) i / 2) hε n hn
  have hB := hsub k μvec π i₀ hi₀ i hi n hn
  have hlog : 0 ≤ Real.log n := log_nat_nonneg_of_two_le hn
  have hgap_sq : 0 < banditGap (gaussianBandit μvec) i ^ 2 :=
    sq_pos_of_pos hi
  have hx : 0 ≤ Real.log n / banditGap (gaussianBandit μvec) i ^ 2 :=
    div_nonneg hlog hgap_sq.le
  have hAarg :
      0 ≤ C₀ *
        (1 + Real.log n /
          (banditGap (gaussianBandit μvec) i / 2) ^ 2) := by positivity
  have hBarg :
      0 ≤ Cᵢ *
        (1 + Real.log n /
          banditGap (gaussianBandit μvec) i ^ 2) := by positivity
  calc
    1 + (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
          ENNReal.ofReal
            (1 / gaussianTSTailProb i₀ s
              (banditArmMean (gaussianBandit μvec) i₀ -
                banditGap (gaussianBandit μvec) i / 2) h - 1)
          ∂banditMeasure (gaussianBandit μvec) π n)
        + ∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
          (if 1 / (n : ℝ) <
              gaussianTSTailProb i s
                (banditArmMean (gaussianBandit μvec) i₀ -
                  banditGap (gaussianBandit μvec) i / 2) h
            then (1 : ℝ≥0∞) else 0)
          ∂banditMeasure (gaussianBandit μvec) π n ≤
        1 +
          ENNReal.ofReal
            (C₀ * (1 + Real.log n /
              (banditGap (gaussianBandit μvec) i / 2) ^ 2)) +
          ENNReal.ofReal
            (Cᵢ * (1 + Real.log n /
              banditGap (gaussianBandit μvec) i ^ 2)) := by
      gcongr
    _ = ENNReal.ofReal
          (1 +
            C₀ * (1 + Real.log n /
              (banditGap (gaussianBandit μvec) i / 2) ^ 2) +
            Cᵢ * (1 + Real.log n /
              banditGap (gaussianBandit μvec) i ^ 2)) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
        ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) hAarg,
        ← ENNReal.ofReal_add (add_nonneg (by positivity : (0 : ℝ) ≤ 1) hAarg) hBarg]
    _ ≤ ENNReal.ofReal
          ((1 + 4 * C₀ + Cᵢ) *
            (1 + Real.log n /
              banditGap (gaussianBandit μvec) i ^ 2)) := by
      apply ENNReal.ofReal_le_ofReal
      have hgap_ne : banditGap (gaussianBandit μvec) i ≠ 0 := ne_of_gt hi
      field_simp [hgap_ne]
      nlinarith [hC₀, hCᵢ, hx]

