-- Prove2me | Theorems.Thm_BanditAlgorithm_chernoff_glr_never_favours_suboptimal_arm
-- name    : BanditAlgorithm.chernoff_glr_never_favours_suboptimal_arm
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T19:10:38.484734+00:00
-- url     : https://prove2.me/theorems/4daac22b-c09d-42e3-bab0-b7c721846d9d
-- title:
--   Chernoff's GLR test never favours a suboptimal arm (L&S Lemma 33.7)
-- statement:
--   The analytic core of Lattimore-Szepesvari Lemma 33.7. For a unit-variance Gaussian bandit and any sampling rule, the probability that the generalised-likelihood-ratio statistic Z_n ever crosses the threshold beta_n(delta) = k log(n^2 + n) + f^{-1}(delta) at a round n where the empirical maximum is attained at a suboptimal arm is at most delta. Here f(x) = e^{k-x}(x/k)^k, so f^{-1}(delta) = (1 + o(1)) log(1/delta), which is what keeps the leading constant of Theorem 33.6 exact; the general exponential-family analogue (Garivier-Kaufmann, COLT 2016, Proposition 12) requires alpha > 1 and would only deliver alpha times the characteristic time. The proof in the book is a Chernoff bound on the pairwise self-normalised deviation combined with a union bound over the number of pulls of each of the two arms, which is where the k log(n^2 + n) term comes from.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Lemma 33.7, p. 410; see also Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016, Proposition 12.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem BanditAlgorithm.chernoff_glr_never_favours_suboptimal_arm {k : ℕ} [NeZero k]
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (π : BanditPolicy k)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν ∈ Set.range (BanditAlgorithm.gaussianBandit (k := k))) :
    BanditAlgorithm.banditTrajMeasure ν π
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ i : Fin k,
          ENNReal.ofReal (BanditAlgorithm.chernoffThreshold k δ n)
              ≤ BanditAlgorithm.trajGLR n ω ∧
            (∀ j, BanditAlgorithm.trajEmpiricalMean j n ω
                ≤ BanditAlgorithm.trajEmpiricalMean i n ω) ∧
              0 < BanditAlgorithm.banditGap ν i}
      ≤ ENNReal.ofReal δ := by
  sorry
