-- Prove2me | solution 1 for BanditAlgorithm.bandit_canonical_occupation_identities
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-07-18T16:55:30.561566+00:00
-- url     : https://prove2.me/submissions/ba3eb7f8-b493-4bb3-be82-e5debcf6c729

import Theorems.Thm_BanditAlgorithm_bandit_expected_reward_eq_arm_occupation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem pullCount_cast_eq_sum_indicator {k n : ℕ} (i : Fin k)
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

private theorem sum_pullCount_cast {k n : ℕ} (h : BanditHistory k n) :
    ∑ i, (armPullCount i h : ℝ) = n := by
  simp_rw [pullCount_cast_eq_sum_indicator]
  rw [Finset.sum_comm]
  simp

private theorem integrable_pullCount {k n : ℕ} (ν : StochasticBandit k)
    (π : BanditPolicy k) (i : Fin k) :
    Integrable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ))
      (banditMeasure ν π n) := by
  apply Integrable.of_mem_Icc 0 n
  · simp_rw [pullCount_cast_eq_sum_indicator]
    have hm : Measurable (fun h : BanditHistory k n ↦
        ∑ t : Fin n, if (h t).1 = i then (1 : ℝ) else 0) := by
      apply Finset.measurable_sum
      intro t ht
      have hcoord : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
        measurable_fst.comp (measurable_pi_apply t)
      exact Measurable.ite ((measurableSet_singleton i).preimage hcoord)
        measurable_const measurable_const
    exact hm.aemeasurable
  · exact Filter.Eventually.of_forall fun h ↦ by
      constructor
      · positivity
      · rw [pullCount_cast_eq_sum_indicator]
        calc
          (∑ t, if (h t).1 = i then (1 : ℝ) else 0) ≤
              ∑ _t : Fin n, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro t ht
                split <;> norm_num
          _ = n := by simp

end BanditAlgorithm

theorem solution {k : ℕ} (ν : BanditAlgorithm.StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditAlgorithm.BanditPolicy k)
    (n : ℕ) :
    (∫ h, (∑ t, (h t).2) ∂(BanditAlgorithm.banditMeasure ν π n) =
      ∑ i, BanditAlgorithm.banditArmMean ν i *
        ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂(BanditAlgorithm.banditMeasure ν π n)) ∧
    (∑ i, ∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
      ∂(BanditAlgorithm.banditMeasure ν π n)) = n := by
  classical
  constructor
  · exact BanditAlgorithm.bandit_expected_reward_eq_arm_occupation ν hInt π n
  · rw [← integral_finset_sum]
    · calc
        ∫ h, (∑ i, (BanditAlgorithm.armPullCount i h : ℝ))
              ∂(BanditAlgorithm.banditMeasure ν π n) =
            ∫ _h, (n : ℝ) ∂(BanditAlgorithm.banditMeasure ν π n) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun h ↦
                BanditAlgorithm.sum_pullCount_cast h
        _ = n := by simp
    · intro i hi
      exact BanditAlgorithm.integrable_pullCount ν π i
