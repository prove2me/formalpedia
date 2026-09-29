-- Prove2me | Theorems.Thm_variance_bernoulli_indicator_eq
-- name    : variance_bernoulli_indicator_eq
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-23T23:36:18.191145+00:00
-- url     : https://prove2.me/theorems/5c6d82b5-f977-4adb-be88-0a0b2c061f9a
-- statement:
--   **Per-coordinate Bernoulli variance.** The $\{0,1\}$-valued indicator $b \mapsto \mathbf{1}\{b = \text{true}\}$ of a single $\mathrm{Bernoulli}(p)$ coordinate has variance
--
--   $$\operatorname{Var}\big[\mathbf{1}\{b\}\big] = p(1-p).$$
--
--   Since the indicator is $\{0,1\}$-valued, $\mathbb{E}[\mathbf{1}^2] = \mathbb{E}[\mathbf{1}] = p$, so $\operatorname{Var} = p - p^2 = p(1-p)$. This is the per-coordinate variance factor that, substituted into the weighted-independent-sum variance, yields the proxy $\sigma^2 = \sum_i c_i^2\, p(1-p)$.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 3; R. van Handel, Probability in High Dimension, §2.1.

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem variance_bernoulli_indicator_eq (p : ℝ≥0) (h : p ≤ 1) :
    variance (fun b : Bool => (cond b 1 0 : ℝ)) (PMF.bernoulli p h).toMeasure
      = (p : ℝ) * (1 - p) := by sorry
