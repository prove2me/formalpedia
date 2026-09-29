-- Prove2me | Theorems.Thm_ConvexOptimization_dualFunction_concave
-- name    : ConvexOptimization.dualFunction_concave
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:32:26.022582+00:00
-- url     : https://prove2.me/theorems/0b240e5c-4b57-4f62-999a-2f2ca2d9347c
-- title:
--   Concavity of the dual function
-- statement:
--   **The Lagrange dual function is concave**, whatever the problem it comes from.
--
--   For the standard problem with objective $f_0$, inequality-constraint functions $f_i$ and equality data $(a_j, b_j)$, let
--
--   $$g(\lambda,\nu) \;=\; \inf_{x \in \mathbb{R}^n}\Bigl[f_0(x) + \sum_{i=1}^{m}\lambda_i f_i(x) + \sum_{j=1}^{p}\nu_j(\langle a_j,x\rangle - b_j)\Bigr] \;\in\; [-\infty,+\infty].$$
--
--   Then for all multiplier pairs $(\lambda_1,\nu_1)$, $(\lambda_2,\nu_2)$ and every $\theta \in (0,1)$,
--
--   $$\theta\, g(\lambda_1,\nu_1) + (1-\theta)\, g(\lambda_2,\nu_2) \;\le\; g\bigl(\theta\lambda_1 + (1-\theta)\lambda_2,\ \theta\nu_1 + (1-\theta)\nu_2\bigr),$$
--
--   the inequality being read in the extended reals.
--
--   Concavity holds with no convexity assumption whatsoever on $f_0$ or the $f_i$: $g$ is a pointwise infimum of functions that are affine in $(\lambda,\nu)$, and such an infimum is always concave. This is why the dual problem — maximize $g$ over $\lambda \succeq 0$ — is a convex problem even when the primal is not, and it is the reason duality is useful for hard nonconvex problems.
--
--   **Formalization Note** $g$ is `EReal`-valued, so the convex combination is formed with `EReal` scalar multiplication and the statement avoids any finiteness hypothesis; the degenerate cases $g = -\infty$ are covered by the arithmetic of the extended reals. Source: B&V §5.1.2, p. 216.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 216, §5.1.2 (the dual function is concave, whatever the primal problem)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.dualFunction_concave {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (lam₁ lam₂ : Fin mm → ℝ) (nu₁ nu₂ : Fin p → ℝ)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (θ : EReal) * dualFunction f₀ fc a b lam₁ nu₁ +
      ((1 - θ : ℝ) : EReal) * dualFunction f₀ fc a b lam₂ nu₂ ≤
    dualFunction f₀ fc a b
      (fun i => θ * lam₁ i + (1 - θ) * lam₂ i)
      (fun j => θ * nu₁ j + (1 - θ) * nu₂ j) := by
  sorry
