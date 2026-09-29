-- Prove2me | Theorems.Thm_variance_weighted_independent_sum_eq
-- name    : variance_weighted_independent_sum_eq
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-23T23:36:11.066276+00:00
-- url     : https://prove2.me/theorems/1d95a2bb-6729-42cc-bad3-cc1af77e04cd
-- statement:
--   **Variance of a coefficient-weighted independent sum (sharp linear Efron–Stein).** For pairwise-independent, square-integrable real random variables $\{X_i\}_{i\in\iota}$ indexed by a finite type, and real coefficients $\{c_i\}$,
--
--   $$\operatorname{Var}\!\Big[\sum_i c_i X_i\Big] = \sum_i c_i^2 \,\operatorname{Var}(X_i).$$
--
--   This is the distribution-dependent (sharp, equality) form of the tensorization of variance specialized to a linear functional — the variance proxy $\sigma^2$ that the worst-case bounded-difference constant cannot capture. It follows from the variance of an independent sum being the sum of variances, composed with $\operatorname{Var}(cX)=c^2\operatorname{Var}(X)$.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550, Princeton), §2.1, Theorem 2.3 (tensorization of variance, equality for linear f); Boucheron–Lugosi–Massart, Concentration Inequalities, Ch. 3.

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem variance_weighted_independent_sum_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (coeff : ι → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Set.Pairwise Set.univ (fun i j => IndepFun (X i) (X j) μ)) :
    variance (fun ω => ∑ i, coeff i * X i ω) μ
      = ∑ i, (coeff i) ^ 2 * variance (X i) μ := by sorry
