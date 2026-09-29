-- Prove2me | Theorems.Thm_ConvexOptimization_log_sum_exp_convexOn
-- name    : ConvexOptimization.log_sum_exp_convexOn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:42:49.224346+00:00
-- url     : https://prove2.me/theorems/55ada2bf-4978-407a-a85a-598083c7e079
-- title:
--   Convexity of log-sum-exp
-- statement:
--   **Convexity of the log-sum-exp function.**
--
--   The function
--
--   $$x \;\longmapsto\; \log\Bigl(\sum_{i=1}^{n} e^{x_i}\Bigr)$$
--
--   is convex on $\mathbb{R}^n$.
--
--   Log-sum-exp is the smooth approximation of the maximum, satisfying $\max_i x_i \le \log\sum_i e^{x_i} \le \max_i x_i + \log n$, so its convexity is a differentiable surrogate for the (also convex, but nonsmooth) maximum function. It is the log-partition function of an exponential family — its gradient is the softmax, its Hessian the covariance of the associated distribution — and it is the Fenchel conjugate of the negative entropy on the probability simplex.
--
--   Together with $\log\det$ it is the most frequently reused convexity fact in the book: geometric programming, logistic regression, maximum-entropy estimation and softmax classifiers all rest on it.
--
--   **Formalization Note** The variable is an element of `EuclideanSpace ℝ (Fin n)` and `x i` denotes its $i$-th coordinate; convexity is asserted on `Set.univ`. Source: B&V §3.1.5, p. 72.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 72, §3.1.5 Examples, the Log-sum-exp item

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.log_sum_exp_convexOn {n : ℕ} :
    ConvexOn ℝ Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) => Real.log (∑ i, Real.exp (x i))) := by
  sorry
