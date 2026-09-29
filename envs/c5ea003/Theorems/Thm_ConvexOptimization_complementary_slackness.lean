-- Prove2me | Theorems.Thm_ConvexOptimization_complementary_slackness
-- name    : ConvexOptimization.complementary_slackness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:34:21.145782+00:00
-- url     : https://prove2.me/theorems/855f043b-fd93-4bd6-b1b8-f2b6a1ad63d8
-- title:
--   Complementary slackness
-- statement:
--   **Complementary slackness** — condition (5.48) of Boyd & Vandenberghe.
--
--   For the standard problem, let $x^{\star}$ be feasible, let $\lambda \in \mathbb{R}^m$ with $\lambda \succeq 0$ and $\nu \in \mathbb{R}^p$, and suppose the duality gap vanishes, $g(\lambda,\nu) = f_0(x^{\star})$, where $g$ is the Lagrange dual function. Then
--
--   $$\lambda_i\, f_i(x^{\star}) \;=\; 0 \qquad (i = 1,\dots,m).$$
--
--   Equivalently: $\lambda_i > 0 \Rightarrow f_i(x^{\star}) = 0$ and $f_i(x^{\star}) < 0 \Rightarrow \lambda_i = 0$. A constraint that is slack at the optimum carries no price, and a constraint with a positive price is active.
--
--   Beyond being one of the four KKT conditions, this is the result that gives dual variables their economic reading as shadow prices, and in practice it is what lets an algorithm identify the active set from a dual solution. No convexity is required: the hypothesis is a zero gap, however obtained.
--
--   **Formalization Note** The zero-gap hypothesis equates the `EReal`-valued dual function with the coercion of the real number $f_0(x^{\star})$, which also encodes finiteness of $g(\lambda,\nu)$; feasibility of $x^{\star}$ is membership in the mission's feasible-set definition. Source: B&V §5.5.2, p. 242, eq. (5.48).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 242, §5.5.2 eq. (5.48) (complementary slackness)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.complementary_slackness {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ feasibleSet fc a b)
    (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i) (nu : Fin p → ℝ)
    (hzero : dualFunction f₀ fc a b lam nu = (f₀ xs : EReal)) :
    ∀ i, lam i * fc i xs = 0 := by
  sorry
