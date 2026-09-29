-- Prove2me | solution 1 for BanditAlgorithm.bandit_kl_ucb_asymptotic_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T02:34:42.379863+00:00
-- url     : https://prove2.me/submissions/ce77167a-cb6e-4475-b11f-e960b9418de3

import Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_finite_regret_bound
import Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_finite_to_asymptotic

open MeasureTheory ProbabilityTheory Filter

/-!
Lattimore--Szepesvári, *Bandit Algorithms*, Theorem 10.6, printed p. 137,
and Exercise 10.2 with its hint on printed pp. 141--142.
-/

theorem solution
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsKLUCBPolicy π) :
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal
          (BanditAlgorithm.banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter
          (fun i ↦ 0 < BanditAlgorithm.banditGap ν i),
        ENNReal.ofReal (BanditAlgorithm.banditGap ν i) /
          ENNReal.ofReal
            (BanditAlgorithm.bernoulliRelativeEntropy
              (BanditAlgorithm.banditArmMean ν i)
              (BanditAlgorithm.banditOptimalMean ν)) := by
  exact BanditAlgorithm.bandit_kl_ucb_finite_to_asymptotic
    μvec hμ ν hν π hπ
    (BanditAlgorithm.bandit_kl_ucb_finite_regret_bound
      μvec hμ ν hν π hπ)
