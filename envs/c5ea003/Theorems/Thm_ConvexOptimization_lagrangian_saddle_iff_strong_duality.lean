-- Prove2me | Theorems.Thm_ConvexOptimization_lagrangian_saddle_iff_strong_duality
-- name    : ConvexOptimization.lagrangian_saddle_iff_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-12T19:33:53.349468+00:00
-- url     : https://prove2.me/theorems/d19677db-8579-4868-bf97-e269f8d0df39
-- title:
--   Saddle-point characterization of strong duality
-- statement:
--   **The saddle-point characterization of strong duality.**
--
--   For the standard problem, write $L(x,\lambda,\nu) = f_0(x) + \sum_i \lambda_i f_i(x) + \sum_j \nu_j(\langle a_j,x\rangle - b_j)$ and $g(\lambda,\nu) = \inf_x L(x,\lambda,\nu)$. Fix $x^{\star} \in \mathbb{R}^n$, $\lambda \in \mathbb{R}^m$ with $\lambda \succeq 0$, and $\nu \in \mathbb{R}^p$. Then $(x^{\star},(\lambda,\nu))$ is a saddle point of $L$ — i.e.
--
--   $$L(x^{\star},\lambda',\nu') \;\le\; L(x^{\star},\lambda,\nu) \;\le\; L(x,\lambda,\nu) \qquad \text{for all } \lambda' \succeq 0,\ \nu' \in \mathbb{R}^p,\ x \in \mathbb{R}^n$$
--
--   — if and only if $x^{\star}$ is feasible, $x^{\star}$ minimizes $f_0$ over the feasible set, and $g(\lambda,\nu) = f_0(x^{\star})$, i.e. the duality gap is zero.
--
--   The equivalence identifies "zero gap with attained optima" with a purely pointwise property of a single function, and it is the step that yields stationarity: at a zero-gap pair, $x^{\star}$ minimizes $L(\cdot,\lambda,\nu)$ over the *whole* space, so for differentiable data its gradient there vanishes — which is precisely the last KKT condition. It also connects this theory to minimax duality, since a saddle point is exactly a point where $\inf\sup$ and $\sup\inf$ agree.
--
--   **Formalization Note** The supremum side of the saddle condition is written as a universally quantified inequality over dual-feasible $(\lambda',\nu')$ rather than as a supremum, avoiding extended-real arithmetic on that side; the zero-gap condition compares the `EReal`-valued dual function with the coercion of $f_0(x^{\star})$. Source: B&V §5.4.2, pp. 239–240.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 239-240, §5.4.2 (saddle-point interpretation; the max-min characterization of strong duality)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.lagrangian_saddle_iff_strong_duality {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (nu : Fin p → ℝ) :
    ((∀ (lam' : Fin mm → ℝ), (∀ i, 0 ≤ lam' i) → ∀ nu' : Fin p → ℝ,
        lagrangian f₀ fc a b xs lam' nu' ≤ lagrangian f₀ fc a b xs lam nu) ∧
     (∀ x, lagrangian f₀ fc a b xs lam nu ≤ lagrangian f₀ fc a b x lam nu)) ↔
    (xs ∈ feasibleSet fc a b ∧ IsMinOn f₀ (feasibleSet fc a b) xs ∧
     dualFunction f₀ fc a b lam nu = (f₀ xs : EReal)) := by
  sorry
