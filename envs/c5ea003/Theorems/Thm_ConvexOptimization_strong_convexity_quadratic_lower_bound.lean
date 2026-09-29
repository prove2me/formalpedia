-- Prove2me | Theorems.Thm_ConvexOptimization_strong_convexity_quadratic_lower_bound
-- name    : ConvexOptimization.strong_convexity_quadratic_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:26:29.596522+00:00
-- url     : https://prove2.me/theorems/21a04905-9e52-4f10-be53-654ca63e6ea8
-- title:
--   Suboptimality bound from strong convexity
-- statement:
--   **Suboptimality is controlled by the gradient norm** — inequality (9.9) of Boyd & Vandenberghe, the standard stopping criterion for unconstrained minimization.
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ have gradient field $g = \nabla f$, and let $m > 0$ be such that $f$ satisfies the strong-convexity lower bound
--
--   $$f(y) \;\ge\; f(x) + \langle \nabla f(x), y - x\rangle + \frac{m}{2}\lVert y - x\rVert_2^{2} \qquad \text{for all } x, y \in \mathbb{R}^n .$$
--
--   Let $x^{\star}$ be a global minimizer of $f$ and write $p^{\star} = f(x^{\star})$ for the optimal value. Then for every $x \in \mathbb{R}^n$
--
--   $$f(x) - p^{\star} \;\le\; \frac{\lVert \nabla f(x)\rVert_2^{2}}{2m} .$$
--
--   The bound converts a computable quantity, the gradient norm at the current iterate, into a certificate of suboptimality: $\lVert \nabla f(x)\rVert_2 \le (2m\varepsilon)^{1/2}$ already guarantees $f(x) - p^{\star} \le \varepsilon$. It is what turns the gradient contraction of Newton's quadratically convergent phase into a bound on the objective error, and hence is used directly in the mission's goal theorem.
--
--   **Formalization Note** The gradient is an explicit field `g` with `∀ x, HasGradientAt f (g x) x`; the minimizer is stated as `IsMinOn f Set.univ xstar`, and $p^{\star}$ appears as `f xstar`. Strong convexity enters as the displayed inequality for all $x,y$ rather than through a Hessian hypothesis, which keeps the statement usable for functions that are not twice differentiable. Source: B&V §9.1.2 p. 460, eq. (9.9).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 460, §9.1.2 eq. (9.9) (suboptimality bounded by the gradient norm)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.strong_convexity_quadratic_lower_bound {n : ℕ} (m : ℝ) (hm : 0 < m)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hsc : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : EuclideanSpace ℝ (Fin n)) :
    f x - f xstar ≤ ‖g x‖ ^ 2 / (2 * m) := by
  sorry
