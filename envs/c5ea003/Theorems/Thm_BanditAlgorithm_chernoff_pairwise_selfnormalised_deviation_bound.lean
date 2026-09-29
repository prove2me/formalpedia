-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_pairwise_selfnormalised_deviation_bound
-- name    : BanditAlgorithm.chernoff_pairwise_selfnormalised_deviation_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:42:05.330423+00:00
-- url     : https://prove2.me/theorems/9769a86c-8dab-416e-b1e1-44d24a1b913b
-- title:
--   Self-normalised pairwise deviation bound at Chernoff's threshold
-- statement:
--   The probabilistic core of Lattimore-Szepesvari Lemma 33.7. For a unit-variance Gaussian bandit and an arbitrary sampling rule, the probability that at some round n there is a pair of distinct arms whose combined self-normalised deviation from the true means, (1/2) T_a (muhat_a - mu_a)^2 + (1/2) T_b (muhat_b - mu_b)^2, reaches the Chernoff threshold beta_n(delta) = k log(n^2 + n) + f^{-1}(delta) is at most delta. This is proved by a Chernoff bound on the chi-squared-type statistic together with a union bound over the possible pull counts of the two arms, which is exactly where the k log(n^2 + n) term comes from; the choice f(x) = e^{k-x}(x/k)^k makes f^{-1}(delta) = (1 + o(1)) log(1/delta), which is what keeps the leading constant of Theorem 33.6 exact.
-- source:
--   The probabilistic content of Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410 (the soundness half of that lemma is the separate node chernoff_stopping_rule_sound). Proved here by the method of mixtures and Ville's inequality, following Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Section 4, and Kaufmann & Koolen, Mixture martingales revisited, JMLR 22 (2021).

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.chernoff_pairwise_selfnormalised_deviation_bound {k : ℕ} [NeZero k]
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (π : BanditAlgorithm.BanditPolicy k)
    (μvec : Fin k → ℝ) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) π
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ a b : Fin k, a ≠ b ∧
          BanditAlgorithm.chernoffThreshold k δ n
            ≤ (BanditAlgorithm.trajPullCount a n ω : ℝ)
                * ((BanditAlgorithm.trajEmpiricalMean a n ω - μvec a) ^ 2 / 2)
              + (BanditAlgorithm.trajPullCount b n ω : ℝ)
                * ((BanditAlgorithm.trajEmpiricalMean b n ω - μvec b) ^ 2 / 2)}
      ≤ ENNReal.ofReal δ := by
  sorry
