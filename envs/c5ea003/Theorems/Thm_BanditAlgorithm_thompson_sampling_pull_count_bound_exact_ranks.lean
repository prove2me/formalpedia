-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_pull_count_bound_exact_ranks
-- name    : BanditAlgorithm.thompson_sampling_pull_count_bound_exact_ranks
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T22:41:36.765572+00:00
-- url     : https://prove2.me/theorems/32e4bdf8-1581-4a20-b801-0ed4c1e3393d
-- title:
--   Thompson-sampling pull-count decomposition with exact realized ranks
-- statement:
--   Assume arm $i_0$ is optimal, let $i\ne i_0$, and fix a separating parameter $\varepsilon$. For Gaussian follow-the-perturbed-leader / Thompson sampling, the expected number of pulls of arm $i$ is bounded by
--
--   $$
--   \mathbb E[T_i(n)]\le 1+
--   \mathbb E\!\left[\sum_{s=0}^{T_{i_0}(n)-1}\left(\frac1{G_{i_0s}}-1\right)\right]
--   +
--   \mathbb E\!\left[\sum_{s=0}^{T_i(n)-1}\mathbf 1\{G_{is}>1/n\}\right].
--   $$
--
--   Here $G_{js}$ is the Gaussian perturbation tail probability above $\mu_{i_0}-\varepsilon$ after the first $s$ observations of arm $j$. Unlike the looser published platform version, each sum stops at the realized pull count. Thus every empirical mean appearing in $G_{js}$ is based on exactly $s$ actual observations, matching the reward-stack rank argument in the proof of Theorem 36.2.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 36.2, Eqs. (36.4)-(36.6), printed pp.464-465. This is the exact rank-sum inequality before enlarging the realized rank ranges to 0,...,n-1 in Eq. (36.3).

import Definitions.Def_BanditPolicy
import Definitions.Def_ThompsonSampling

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.thompson_sampling_pull_count_bound_exact_ranks {k : ℕ} [NeZero k]
    (ν : StochasticBandit k) {π : BanditPolicy k} (hπ : IsGaussianTSPolicy π)
    (i₀ : Fin k) (h₀ : banditArmMean ν i₀ = banditOptimalMean ν)
    (i : Fin k) (hi : i ≠ i₀) (ε : ℝ) (n : ℕ) :
    ∫⁻ h, (armPullCount i h : ℝ≥0∞) ∂banditMeasure ν π n ≤
      1 + (∫⁻ h, ∑ s ∈ Finset.range (armPullCount i₀ h),
            ENNReal.ofReal (1 / gaussianTSTailProb i₀ s
              (banditArmMean ν i₀ - ε) h - 1)
            ∂banditMeasure ν π n)
        + ∫⁻ h, ∑ s ∈ Finset.range (armPullCount i h),
            (if 1 / (n : ℝ) <
                gaussianTSTailProb i s (banditArmMean ν i₀ - ε) h
              then (1 : ℝ≥0∞) else 0)
            ∂banditMeasure ν π n := by
  sorry
