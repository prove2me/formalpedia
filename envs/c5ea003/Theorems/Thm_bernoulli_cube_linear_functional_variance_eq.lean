-- Prove2me | Theorems.Thm_bernoulli_cube_linear_functional_variance_eq
-- name    : bernoulli_cube_linear_functional_variance_eq
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-23T23:36:25.100709+00:00
-- url     : https://prove2.me/theorems/b2e21597-5fbe-426d-badf-b1a9bed3b9ff
-- statement:
--   **$\sigma^2$-proxy on the finite Bernoulli product cube (capstone).** On the product Bernoulli cube $(\iota \to \mathrm{Bool})$ with the independent-coordinate measure $\bigotimes_i \mathrm{Bernoulli}(p)$, the variance of the linear functional $\omega \mapsto \sum_i c_i\, \mathbf{1}\{\omega_i\}$ equals
--
--   $$\operatorname{Var}\!\Big[\sum_i c_i\,\mathbf{1}\{\omega_i\}\Big] = \Big(\sum_i c_i^2\Big)\, p(1-p).$$
--
--   This is the **variance-aware proxy $\sigma^2 = \sum_i c_i^2\, p(1-p)$** — exactly the distribution-dependent second moment that the worst-case bounded-difference constant $V = \sum_i c_i^2$ over-estimates by the factor $1/(p(1-p))$ in the sparse regime. It is obtained by tensorization of variance over the product measure (the per-coordinate variances of the independent Bernoulli summands add), each per-coordinate term being $c_i^2\, p(1-p)$. This grounds the variance hypothesis $\sum_i c_i^2\, p(1-p) \le \sigma^2$ that downstream $\sigma^2$-aware concentration (modified log-Sobolev / Talagrand) takes as given.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550, Princeton), §2.1, Theorem 2.3 (tensorization of variance); Boucheron–Lugosi–Massart, Concentration Inequalities, Ch. 3, Theorem 3.1.

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem bernoulli_cube_linear_functional_variance_eq
    {ι : Type*} [Fintype ι] (p : ℝ≥0) (h : p ≤ 1) (coeff : ι → ℝ) :
    variance (fun ω : ι → Bool => ∑ i, coeff i * (cond (ω i) 1 0 : ℝ))
        (Measure.pi (fun _ : ι => (PMF.bernoulli p h).toMeasure))
      = (∑ i, (coeff i) ^ 2) * ((p : ℝ) * (1 - p)) := by sorry
