-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussianBandit_mean_gap_dictionary
-- name    : BanditAlgorithm.gaussianBandit_mean_gap_dictionary
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:21:31.36792+00:00
-- url     : https://prove2.me/theorems/711e8db2-9342-4a91-b4e3-8fbc34cfbe43
-- title:
--   Means, gaps and optimal arms of a Gaussian bandit
-- statement:
--   The dictionary between the Gaussian bandit $\nu=\mathcal N(\mu_1,1)\otimes\cdots\otimes\mathcal N(\mu_k,1)$ and its parameter vector $\mu\in\mathbb R^k$: the arm means of $\nu$ are $\mu_i$, the suboptimality gaps are
--   $$\Delta_i=\max_j\mu_j-\mu_i,$$
--   and arm $i$ is suboptimal ($\Delta_i>0$) exactly when some other arm has a strictly larger parameter.
--
--   Every statement about the Gaussian class $\mathcal E^k_{\mathcal N}(1)$ is phrased through $\mu$, while the general framework of Chapter 33 is phrased through the abstract means and gaps of a `StochasticBandit`. This lemma is the translation between the two, and is used at essentially every step of the Track-and-Stop analysis.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Sections 4.4, 4.5 and 33.1.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal

theorem BanditAlgorithm.gaussianBandit_mean_gap_dictionary {k : ℕ} [NeZero k]
    (μvec : Fin k → ℝ) (i : Fin k) :
    BanditAlgorithm.banditArmMean (BanditAlgorithm.gaussianBandit μvec) i = μvec i ∧
      BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i
          = (⨆ j, μvec j) - μvec i ∧
        (0 < BanditAlgorithm.banditGap (BanditAlgorithm.gaussianBandit μvec) i
          ↔ ∃ j, μvec i < μvec j) ∧
          (i ∈ BanditAlgorithm.banditOptimalArms (BanditAlgorithm.gaussianBandit μvec)
            ↔ ∀ j, μvec j ≤ μvec i) := by
  sorry
