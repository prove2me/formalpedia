-- Prove2me | Theorems.Thm_BanditAlgorithm_gaussianBandit_isSubgaussian_one
-- name    : BanditAlgorithm.gaussianBandit_isSubgaussian_one
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-30T23:04:01.786086+00:00
-- url     : https://prove2.me/theorems/1d7a6b11-5cf2-47dc-ad42-47db668ce480
-- title:
--   Unit-variance Gaussian bandits are 1-subgaussian
-- statement:
--   Let $\mu=(\mu_1,\ldots,\mu_k)$ be any real mean vector, and let arm $i$ have reward law $\mathcal N(\mu_i,1)$. Then every centered reward $X_i-\mu_i$ has moment-generating function
--
--   $$
--   \mathbb E\!\left[e^{\lambda(X_i-\mu_i)}\right]=e^{\lambda^2/2}.
--   $$
--
--   Consequently the Gaussian bandit is $1$-subgaussian: all arm rewards are integrable and their centered moment-generating functions are bounded by $e^{\lambda^2/2}$.
--
--   This packages the standard Gaussian MGF calculation in the stochastic-bandit interface for reuse by adaptive concentration theorems.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Example 5.6 and Gaussian moment-generating-function calculation, printed p. 75 / PDF p. 84; unit-variance Gaussian bandit class used in Theorem 36.3, printed p. 465 / PDF p. 474.

import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- Every unit-variance Gaussian bandit is 1-subgaussian. -/
theorem gaussianBandit_isSubgaussian_one {k : ℕ} (μvec : Fin k → ℝ) :
    IsSubgaussianBandit 1 (gaussianBandit μvec) := by
  sorry

end BanditAlgorithm
