-- Prove2me | Theorems.Thm_BanditAlgorithm_thompson_sampling_gaussian_minimax_regret
-- name    : BanditAlgorithm.thompson_sampling_gaussian_minimax_regret
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T19:53:09.88617+00:00
-- url     : https://prove2.me/theorems/5f9f9537-90df-4d65-80b5-af1855612170
-- title:
--   Distribution-free regret bound for Gaussian Thompson Sampling
-- statement:
--   There is a universal constant $C>0$ such that Gaussian Thompson sampling on every $k$-armed unit-variance Gaussian bandit with means in $[0,1]$ satisfies, for every horizon $n\ge2$,
--
--   $$
--   R_n\le C\sqrt{k n\log n}.
--   $$
--
--   This is the distribution-free companion to the instance-dependent logarithmic asymptotic bound. The normalization of the means controls the regret of the algorithm's forced initialization, while the lower bound $n\ge2$ avoids the degenerate logarithmic right-hand side at horizon one.
--
--   **Formalization Note** The existential constant is uniform over the number of arms, the normalized mean vector, the policy implementation satisfying `IsGaussianTSPolicy`, and the horizon.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 36.3, distribution-free bound in Eq. (36.6), printed p. 465, with the bounded-mean normalization of Theorem 36.1, printed p. 459.

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit
import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.thompson_sampling_gaussian_minimax_regret :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π → (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ n : ℕ, 2 ≤ n →
        banditRegret (gaussianBandit μvec) π n ≤
          C * Real.sqrt (k * n * Real.log n) := by
  sorry
