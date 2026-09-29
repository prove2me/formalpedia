-- Prove2me | Theorems.Thm_ConvexOptimization_scalarization_sufficient_pareto
-- name    : ConvexOptimization.scalarization_sufficient_pareto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:35:47.476024+00:00
-- url     : https://prove2.me/theorems/9171d4df-2ca3-452d-92ff-4e9f3c929cde
-- title:
--   Pareto optimality via scalarization
-- statement:
--   **Scalarization produces Pareto optimal points.**
--
--   Let $X \subseteq \mathbb{R}^n$ and let $f : \mathbb{R}^n \to \mathbb{R}^{k}$ be a vector objective with components $f_1,\dots,f_k$. Fix weights $\lambda \in \mathbb{R}^{k}$ with $\lambda_i > 0$ for every $i$, and suppose $x^{\star} \in X$ minimizes the scalarized objective:
--
--   $$\sum_{i=1}^{k} \lambda_i f_i(x^{\star}) \;\le\; \sum_{i=1}^{k}\lambda_i f_i(y) \qquad \text{for every } y \in X .$$
--
--   Then $x^{\star}$ is Pareto optimal for $f$: there is no $y \in X$ with $f_i(y) \le f_i(x^{\star})$ for all $i$ and $f(y) \ne f(x^{\star})$ — no feasible point improves some component without worsening another.
--
--   Scalarization is the standard device for reducing multicriterion optimization to the single-objective theory of this mission: choosing strictly positive weights and solving one ordinary problem yields a Pareto point, and sweeping the weights traces out a family of them. Strict positivity is essential — with a zero weight the minimizer may be dominated in the ignored coordinate.
--
--   **Formalization Note** The vector objective is a function into `Fin k → ℝ`; domination is expressed as componentwise $\le$ together with $f(y) \ne f(x^{\star})$ as functions, and the conclusion is the negation of an existential. No convexity of $X$ or of the components is needed for this direction. Source: B&V §4.7.4, p. 178.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 178, §4.7.4 (scalarization; finding Pareto optimal points by minimizing a positively weighted sum)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.scalarization_sufficient_pareto {n k : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → Fin k → ℝ)
    (lam : Fin k → ℝ) (hlam : ∀ i, 0 < lam i)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ X)
    (hmin : ∀ y ∈ X, ∑ i, lam i * f xs i ≤ ∑ i, lam i * f y i) :
    ¬∃ y ∈ X, (∀ i, f y i ≤ f xs i) ∧ f y ≠ f xs := by
  sorry
