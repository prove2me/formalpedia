-- Prove2me | Theorems.Thm_ConvexOptimization_slater_supporting_multipliers
-- name    : ConvexOptimization.slater_supporting_multipliers
-- status  : Proved
-- author  : @Yifan Hong
-- created : 2026-08-14T14:08:38.65248+00:00
-- url     : https://prove2.me/theorems/cb4e8c32-fd56-4914-aeaf-1de7c5e82640
-- title:
--   Slater supporting multipliers: normalized separation certificate
-- statement:
--   Let $f_0:\mathbb R^n\to\mathbb R$ and $f_i:\mathbb R^n\to\mathbb R$ be convex, and impose the affine equalities $\langle a_j,x\rangle=b_j$ with linearly independent normals $a_j$. Suppose there is a Slater point $\tilde x$ satisfying every inequality strictly and every equality exactly, and suppose the primal objective is bounded below on the feasible set. Write
--
--   $$
--   p^\star=\inf\{f_0(x): f_i(x)\le 0,\ \langle a_j,x\rangle=b_j\}.
--   $$
--
--   Then there are inequality multipliers $\lambda_i\ge 0$ and equality multipliers $\nu_j\in\mathbb R$ such that the Lagrangian has the global lower bound
--
--   $$
--   p^\star\le L(x,\lambda,\nu)
--    =f_0(x)+\sum_i\lambda_i f_i(x)
--      +\sum_j\nu_j(\langle a_j,x\rangle-b_j)
--   \qquad\text{for every }x\in\mathbb R^n.
--   $$
--
--   This is the normalized supporting-hyperplane certificate used to derive strong duality and dual attainment under Slater's condition.
--
--   **Formalization Note** The primal value is represented by the real infimum `sInf (f₀ '' feasibleSet fc a b)`; the conclusion is kept real-valued so it can be reused independently of the `EReal` representation of the dual function.
-- source:
--   Boyd and Vandenberghe, Convex Optimization (2004; seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf, Section 5.3.2, pp. 235-236, normalized consequence of equation (5.41); Slater condition rules out the vertical case on p. 236.

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.slater_supporting_multipliers {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs_ineq : ∀ i, fc i xs < 0)
    (hxs_eq : ∀ j, ⟪a j, xs⟫ = b j)
    (hbdd : BddBelow (f₀ '' feasibleSet fc a b)) :
    ∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧
      ∀ x, sInf (f₀ '' feasibleSet fc a b) ≤ lagrangian f₀ fc a b x lam nu := by sorry
