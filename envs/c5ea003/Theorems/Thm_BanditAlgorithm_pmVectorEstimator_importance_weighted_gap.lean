-- Prove2me | Theorems.Thm_BanditAlgorithm_pmVectorEstimator_importance_weighted_gap
-- name    : BanditAlgorithm.pmVectorEstimator_importance_weighted_gap
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T20:26:07.641571+00:00
-- url     : https://prove2.me/theorems/0f88f483-88e5-45b0-b697-4ec4c1151143
-- title:
--   Importance-weighted vector estimators are unbiased for loss differences
-- statement:
--   Let $S$ be the finite comparator set used by Algorithm 26, let $q$ be a probability distribution supported on $S$, let $p$ be a strictly positive sampling distribution, and let $f$ be a vector loss estimator on $S$. For an outcome $i$ and comparator $b\in S$, importance weighting is unbiased for the $q$-averaged loss difference:
--
--   $$
--   \sum_a p_a\sum_c q_c\left(
--   \frac{f(a,\Phi_{ai})_c}{p_a}-
--   \frac{f(a,\Phi_{ai})_b}{p_a}
--   \right)
--   =
--   \sum_c q_c(L_{ci}-L_{bi}).
--   $$
--
--   Strict positivity of $p$ justifies cancellation of the importance weights. The common additive shift allowed in the vector-estimator definition cancels from every loss difference; coordinates outside $S$ contribute zero because $q$ is supported on $S$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), §37.5 printed pp. 492–495, vector-estimator definition and proof of Theorem 37.15, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_PartialMonitoringAlgorithm26

open scoped BigOperators

namespace BanditAlgorithm

theorem pmVectorEstimator_importance_weighted_gap
    {k d : ℕ} {𝕊 : Type*}
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k))
    (q p : Fin k → ℝ) (f : Fin k → 𝕊 → Fin k → ℝ)
    (hq : PMSupportedOn S q) (hp : PMInteriorDistribution p)
    (hf : PMVectorEstimatorOn G S f) (i : Fin d) (b : Fin k) (hb : b ∈ S) :
    ∑ a : Fin k, p a *
        (∑ c : Fin k, q c *
          (f a (G.Φ a i) c / p a - f a (G.Φ a i) b / p a)) =
      ∑ c : Fin k, q c * (G.L c i - G.L b i) := by sorry
