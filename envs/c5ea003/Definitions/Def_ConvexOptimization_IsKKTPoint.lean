-- Prove2me | Definitions.Def_ConvexOptimization_IsKKTPoint
-- name    : ConvexOptimization_IsKKTPoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-12T19:30:54.004019+00:00
-- url     : https://prove2.me/theorems/79b384f1-9cb8-44c3-ab0e-1bc5efb359e0
-- title:
--   KKT point
-- statement:
--   The **Karush–Kuhn–Tucker conditions** for the standard differentiable problem, packaged as a predicate on a triple $(x,\lambda,\nu)$.
--
--   Consider minimizing $f_0$ subject to $f_i(x) \le 0$ $(i = 1,\dots,m)$ and $\langle a_j, x\rangle = b_j$ $(j = 1,\dots,p)$ on $\mathbb{R}^n$, and let $\nabla f_0$ and $\nabla f_i$ denote the gradient fields of the objective and of the inequality-constraint functions. The triple $(x, \lambda, \nu) \in \mathbb{R}^n \times \mathbb{R}^m \times \mathbb{R}^p$ is a *KKT point* when
--
--   $$f_i(x) \le 0, \qquad \langle a_j, x\rangle = b_j, \qquad \lambda_i \ge 0, \qquad \lambda_i f_i(x) = 0, \qquad \nabla f_0(x) + \sum_{i=1}^{m}\lambda_i \nabla f_i(x) + \sum_{j=1}^{p}\nu_j a_j = 0,$$
--
--   for all $i$ and $j$ — respectively primal feasibility, dual feasibility, complementary slackness, and stationarity of the Lagrangian $L(\cdot,\lambda,\nu)$ at $x$.
--
--   These are conditions (5.49) of Boyd & Vandenberghe. For a general problem they are necessary at any optimal point with zero duality gap; for a convex problem they are also sufficient, and under Slater's condition they characterize optimality exactly — which is the goal of this mission. They are what solvers and analytical derivations alike actually check.
--
--   **Formalization Note** The gradient fields `f₀'` and `fc'` are explicit arguments rather than derived from $f_0$, $f_i$; theorems using the predicate tie them to the functions with `HasGradientAt` hypotheses. The stationarity condition is an equation in `EuclideanSpace ℝ (Fin n)` with scalar multiplication `•`, and the equality constraints appear as inner products against the vectors `a j`.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 243-244, §5.5.3 eq. (5.49) (the Karush-Kuhn-Tucker conditions)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- KKT point for the standard differentiable problem (B&V §5.5.3): primal and
dual feasibility, complementary slackness, and stationarity of the Lagrangian.
`f₀'`/`fc'` are the gradient fields of the objective and the constraints. -/
def IsKKTPoint {n mm p : ℕ}
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (f₀' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (fc' : Fin mm → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (lam : Fin mm → ℝ) (nu : Fin p → ℝ) : Prop :=
  (∀ i, fc i x ≤ 0) ∧ (∀ j, ⟪a j, x⟫ = b j) ∧ (∀ i, 0 ≤ lam i) ∧
  (∀ i, lam i * fc i x = 0) ∧
  f₀' x + ∑ i, lam i • fc' i x + ∑ j, nu j • a j = 0

end ConvexOptimization


