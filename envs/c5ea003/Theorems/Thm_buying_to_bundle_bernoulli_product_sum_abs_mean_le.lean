-- Prove2me | Theorems.Thm_buying_to_bundle_bernoulli_product_sum_abs_mean_le
-- name    : buying_to_bundle_bernoulli_product_sum_abs_mean_le
-- status  : Proved
-- author  : @ann
-- created : 2026-07-04T01:51:17.178157+00:00
-- url     : https://prove2.me/theorems/32956d1c-22c3-40d2-bd8c-7da785bd7e16
-- statement:
--   Conditional finite-product Bernoulli fluctuation bound for Equation (5) of *Buying to Bundle: Optimal Sourcing from Monopolistic Sellers*, Appendix C.2 p. 35. For fixed qualities $a_i \in [0,\mu_H]$ and independent inclusion probabilities $p_i \in [0,1]$, the explicit finite mixture over inclusion patterns satisfies $E_I\,|\sum_i I_i a_i - \sum_i p_i a_i| \le \mu_H\sqrt N$. The paper proves this by $E_I Y=\sum_i p_i a_i$, $\operatorname{Var}(Y)=\sum_i p_i(1-p_i)a_i^2\le N\mu_H^2$, and Cauchy-Schwarz/Jensen.
-- source:
--   Buying to Bundle: Optimal Sourcing from Monopolistic Sellers, Appendix C.2, proof of Theorem 4.6, p. 35, Eq. (5)

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

open MeasureTheory
open scoped BigOperators

theorem buying_to_bundle_bernoulli_product_sum_abs_mean_le
    {N : ℕ} {μH : ℝ} (hμH0 : 0 ≤ μH)
    (p a : Fin N → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha0 : ∀ i, 0 ≤ a i) (haH : ∀ i, a i ≤ μH) :
    (∑ I : Fin N → Bool,
        (∏ i, if I i then p i else 1 - p i) *
          |(∑ i, if I i then a i else 0) - ∑ i, p i * a i|) ≤
      μH * Real.sqrt N := by sorry
