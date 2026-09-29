-- Prove2me | Theorems.Thm_ConvexOptimization_gradient_descent_exact_linear_rate
-- name    : ConvexOptimization.gradient_descent_exact_linear_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:27:02.664579+00:00
-- url     : https://prove2.me/theorems/59f02a6b-736b-4de1-9945-abe463849ede
-- title:
--   Gradient descent with exact line search: linear rate
-- statement:
--   **Linear convergence of gradient descent with exact line search.**
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ with gradient field $\nabla f$ satisfy, for constants $0 < m \le M$, the two-sided quadratic bounds
--
--   $$f(x) + \langle \nabla f(x), y - x\rangle + \frac{m}{2}\lVert y - x\rVert_2^2 \;\le\; f(y) \;\le\; f(x) + \langle \nabla f(x), y - x\rangle + \frac{M}{2}\lVert y - x\rVert_2^2 \qquad (x, y \in \mathbb{R}^n),$$
--
--   i.e. $f$ is $m$-strongly convex and $M$-smooth. Let $x^{\star}$ be a global minimizer, $p^{\star} = f(x^{\star})$, and let $(x_k)$ be a gradient-descent sequence with exact line search: each iterate has the form $x_{k+1} = x_k - t\,\nabla f(x_k)$ for some $t \ge 0$ and is optimal along the ray, $f(x_{k+1}) \le f(x_k - s\,\nabla f(x_k))$ for every $s \ge 0$. Then for every $k$
--
--   $$f(x_k) - p^{\star} \;\le\; \Bigl(1 - \frac{m}{M}\Bigr)^{k}\bigl(f(x_0) - p^{\star}\bigr).$$
--
--   The error decays geometrically with ratio $1 - m/M$, so the iteration count to reach accuracy $\varepsilon$ scales with the condition number $M/m$ and with $\log(1/\varepsilon)$. This is the benchmark against which the mission's goal theorem — Newton's dimension-free, $\log\log(1/\varepsilon)$ count — is to be read.
--
--   **Formalization Note** Exact line search is expressed as the conjunction of "the step is along $-\nabla f(x_k)$ with a nonnegative step size" and "no nonnegative step size along that ray gives a smaller value", which avoids assuming a minimizer of the line-search subproblem exists as a chosen value. The minimizer is `IsMinOn f Set.univ xstar`. Source: B&V §9.3.1, pp. 467–468.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 467-468, §9.3.1 eq. (9.18) (gradient descent with exact line search: linear convergence with ratio 1 - m/M)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.gradient_descent_exact_linear_rate {n : ℕ} (m M : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hsc : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hsm : ∀ x y : EuclideanSpace ℝ (Fin n),
      f y ≤ f x + ⟪g x, y - x⟫ + M / 2 * ‖y - x‖ ^ 2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hstep : ∀ k, (∃ t : ℝ, 0 ≤ t ∧ x (k + 1) = x k - t • g (x k)) ∧
      ∀ s : ℝ, 0 ≤ s → f (x (k + 1)) ≤ f (x k - s • g (x k))) :
    ∀ k, f (x k) - f xstar ≤ (1 - m / M) ^ k * (f (x 0) - f xstar) := by
  sorry
