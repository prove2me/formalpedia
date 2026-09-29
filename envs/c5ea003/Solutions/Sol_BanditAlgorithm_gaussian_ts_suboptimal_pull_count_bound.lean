-- Prove2me | solution 1 for BanditAlgorithm.gaussian_ts_suboptimal_pull_count_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T22:45:55.934279+00:00
-- url     : https://prove2.me/submissions/70688ad1-723b-4317-b06f-0112011ead9e

import Theorems.Thm_BanditAlgorithm_thompson_sampling_pull_count_bound_exact_ranks
import Theorems.Thm_BanditAlgorithm_gaussian_ts_exact_rank_tail_sums_bound

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator_exact {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) :
    (armPullCount i h : ℝ) = ∑ t, if (h t).1 = i then 1 else 0 := by
  classical
  rw [armPullCount]
  have hset : {t | (h t).1 = i}.toFinset =
      Finset.univ.filter (fun t ↦ (h t).1 = i) := by
    ext t
    simp
  rw [hset]
  simpa using
    (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i) Finset.univ).symm

private theorem measurable_armPullCount_cast_exact {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then 1 else 0 by
    funext h
    exact pullCount_cast_eq_sum_indicator_exact i h]
  apply Finset.measurable_sum
  intro t _
  exact Measurable.ite
    ((measurableSet_singleton i).preimage
      (measurable_fst.comp (measurable_pi_apply t)))
    measurable_const measurable_const

private theorem armPullCount_le_horizon_exact {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) : armPullCount i h ≤ n := by
  change ({t | (h t).1 = i}.toFinset : Finset (Fin n)).card ≤ n
  simpa using
    (Finset.card_le_univ ({t | (h t).1 = i}.toFinset : Finset (Fin n)))

private theorem integrable_armPullCount_exact {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · exact (measurable_armPullCount_cast_exact i).aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · exact_mod_cast armPullCount_le_horizon_exact i h

theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        IsGaussianTSPolicy π →
        ∀ (i : Fin k), 0 < banditGap (gaussianBandit μvec) i →
          ∀ n : ℕ, 2 ≤ n →
            ∫ h, (armPullCount i h : ℝ)
                ∂banditMeasure (gaussianBandit μvec) π n ≤
              C * (1 + Real.log n /
                banditGap (gaussianBandit μvec) i ^ 2) := by
  obtain ⟨C, hC, htail⟩ := gaussian_ts_exact_rank_tail_sums_bound
  refine ⟨C, hC, ?_⟩
  intro k _ μvec π hπ i hi n hn
  let ν := gaussianBandit μvec
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (banditArmMean ν)
      ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩, Finset.mem_univ _⟩
  have hopt : banditArmMean ν i₀ = banditOptimalMean ν := by
    apply le_antisymm
    · exact le_ciSup (Finite.bddAbove_range (fun j ↦ banditArmMean ν j)) i₀
    · unfold banditOptimalMean
      exact ciSup_le fun j ↦ hi₀ j (Finset.mem_univ j)
  have hine : i ≠ i₀ := by
    intro h
    subst i
    rw [banditGap, hopt] at hi
    linarith
  have hdecomp :=
    thompson_sampling_pull_count_bound_exact_ranks ν hπ i₀ hopt i hine
      (banditGap ν i / 2) n
  have hlin :
      (∫⁻ h, (armPullCount i h : ℝ≥0∞) ∂banditMeasure ν π n) ≤
        ENNReal.ofReal (C * (1 + Real.log n / banditGap ν i ^ 2)) :=
    hdecomp.trans (htail k μvec π hπ i₀ hopt i hi n hn)
  have hInt := integrable_armPullCount_exact (n := n) ν π i
  have hof :
      ENNReal.ofReal
          (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) =
        ∫⁻ h, (armPullCount i h : ℝ≥0∞) ∂banditMeasure ν π n := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun h ↦ by positivity)]
    apply lintegral_congr
    intro h
    simp
  have hRHS :
      0 ≤ C * (1 + Real.log n / banditGap ν i ^ 2) := by
    have hnR : (1 : ℝ) < n := by
      exact_mod_cast lt_of_lt_of_le (by omega : 1 < 2) hn
    have : 0 < Real.log (n : ℝ) := Real.log_pos hnR
    positivity
  apply (ENNReal.ofReal_le_ofReal_iff hRHS).mp
  rw [hof]
  exact hlin

end BanditAlgorithm
