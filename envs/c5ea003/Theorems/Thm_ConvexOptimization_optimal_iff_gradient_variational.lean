-- Prove2me | Theorems.Thm_ConvexOptimization_optimal_iff_gradient_variational
-- name    : ConvexOptimization.optimal_iff_gradient_variational
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:31:28.232986+00:00
-- url     : https://prove2.me/theorems/8f20c469-ea0b-4139-9eef-970448a48225
-- title:
--   First-order optimality criterion
-- statement:
--   **The first-order optimality criterion** for differentiable convex problems — inequality (4.21) of Boyd & Vandenberghe.
--
--   Let $X \subseteq \mathbb{R}^n$ be convex, let $f : \mathbb{R}^n \to \mathbb{R}$ be differentiable with gradient field $\nabla f$, and assume $f$ is convex on $X$. Then for $x \in X$,
--
--   $$x \text{ minimizes } f \text{ over } X \qquad\Longleftrightarrow\qquad \langle \nabla f(x),\, y - x\rangle \ge 0 \quad \text{for every } y \in X .$$
--
--   Geometrically the condition says that $-\nabla f(x)$ defines a supporting hyperplane of $X$ at $x$: moving from $x$ toward any other feasible point cannot decrease $f$ to first order. For an unconstrained problem ($X = \mathbb{R}^n$) it collapses to $\nabla f(x) = 0$.
--
--   This is the bridge between the variational and the algebraic descriptions of optimality, and it is used in both directions in this mission — to convert stationarity of the Lagrangian into optimality of a KKT point, and to characterize Euclidean projection.
--
--   **Formalization Note** The gradient is an explicit field `f'` with `∀ x, HasGradientAt f (f' x) x`, and optimality is `IsMinOn f X x`. Convexity of the domain is assumed separately as `Convex ℝ X` alongside `ConvexOn ℝ X f`. Source: B&V §4.2.3, p. 139, eq. (4.21).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 139, §4.2.3 eq. (4.21) (first-order optimality criterion for differentiable convex problems)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.optimal_iff_gradient_variational {n : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (f' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ∀ x, HasGradientAt f (f' x) x) (hfc : ConvexOn ℝ X f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) :
    IsMinOn f X x ↔ ∀ y ∈ X, 0 ≤ ⟪f' x, y - x⟫ := by
  sorry
