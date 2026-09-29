-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussian_exact_rank_reciprocal_tail_expectation_bound
-- name    : BanditAlgorithm.gaussian_exact_rank_reciprocal_tail_expectation_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T23:08:12.667249+00:00
-- url     : https://prove2.me/theorems/37f7f80c-0adf-4271-a6fb-bedb5536ebf4
-- title:
--   One-rank Gaussian reciprocal posterior-tail estimate
-- statement:
--   Consider an arbitrary adaptive policy on a unit-variance Gaussian bandit. Fix an arm $i$, a realized reward rank $s\ge1$, and $\varepsilon>0$. Let $G_{i,s}(\mu_i-\varepsilon)$ be the posterior Gaussian probability of exceeding $\mu_i-\varepsilon$ after the first $s$ rewards of arm $i$. There is a universal constant $C>0$ such that, at every horizon $n$,
--
--   $$
--   \mathbb E\!\left[
--   \mathbf 1\{s<T_i(n)\}
--   \left(\frac{1}{G_{i,s}(\mu_i-\varepsilon)}-1\right)_+
--   \right]
--   \le \frac{C}{s\varepsilon^2}.
--   $$
--
--   The event $s<T_i(n)$ ensures that the posterior mean uses exactly $s$ realized rewards. Summing this rankwise estimate gives the finite-horizon optimal-arm reciprocal-tail bound used in Gaussian Thompson sampling.
--
--   **Formalization Note** The nonnegative expectation is encoded as a `lintegral`.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 36.6(a) and the Gaussian lower-tail hint, printed p. 475 / PDF p. 484; reward-stack convention in Section 4.6 and Theorem 36.2, printed pp. 463–465 / PDF pp. 472–474. This is the fixed-rank estimate whose harmonic summation yields the finite-horizon form of Exercise 36.6(a).

import Definitions.Def_ThompsonSampling
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

/-- One-rank Gaussian reciprocal-posterior-tail estimate. -/
theorem gaussian_exact_rank_reciprocal_tail_expectation_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
        ∀ (i : Fin k) (s : ℕ), 0 < s →
        ∀ ε : ℝ, 0 < ε →
        ∀ n : ℕ,
          (∫⁻ h,
              if s < armPullCount i h then
                ENNReal.ofReal
                  (1 / gaussianTSTailProb i s
                    (banditArmMean (gaussianBandit μvec) i - ε) h - 1)
              else 0
              ∂banditMeasure (gaussianBandit μvec) π n) ≤
            ENNReal.ofReal (C / ((s : ℝ) * ε ^ 2)) := by
  sorry

end BanditAlgorithm
