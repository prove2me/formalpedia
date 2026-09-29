-- Prove2me | Theorems.Thm_ConvexOptimization_strong_alternatives_strict_convex
-- name    : ConvexOptimization.strong_alternatives_strict_convex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:03:12.564+00:00
-- url     : https://prove2.me/theorems/5fc2f8d0-9e15-403b-912e-9b9884ce89ba
-- title:
--   Strong alternatives for strict convex inequality systems
-- statement:
--   **Strong alternatives for a system of strict convex inequalities.**
--
--   Let $f_1,\dots,f_m : \mathbb{R}^n \to \mathbb{R}$ be convex, let $a_1,\dots,a_p \in \mathbb{R}^n$ be linearly independent, let $b \in \mathbb{R}^p$, and assume the affine system $\langle a_j, x\rangle = b_j$ has a solution. Write $g(\lambda,\nu) = \inf_x\bigl[\sum_i \lambda_i f_i(x) + \sum_j \nu_j(\langle a_j,x\rangle - b_j)\bigr]$ for the dual function of the *feasibility* problem, i.e. of the problem with zero objective. Then
--
--   $$\bigl(\exists x:\ f_i(x) < 0 \ \forall i,\ \langle a_j,x\rangle = b_j \ \forall j\bigr) \qquad\Longleftrightarrow\qquad \neg\bigl(\exists \lambda \succeq 0,\ \lambda \ne 0,\ \nu:\ g(\lambda,\nu) \ge 0\bigr).$$
--
--   The two systems are *strong* alternatives: exactly one of them is feasible, with no gap between them. The second is the certificate of infeasibility — a nonnegative, nonzero combination of the constraints that is bounded below by zero, i.e. a proof that no strictly feasible point exists.
--
--   Theorems of the alternative are the infeasibility counterpart of duality: rather than certifying optimality, they certify that a system has no solution. Farkas' lemma is the linear case, and the LMI alternatives used later in this mission are the semidefinite specializations of this result.
--
--   **Formalization Note** The dual function is the mission's `dualFunction` applied with objective `0`, so the statement reuses the Lagrange-duality interface of Mission II; the constraint qualification is stated as solvability of the equality system together with linear independence of the `a j`. Source: B&V §5.8.2, pp. 260–261, systems (5.79)/(5.80).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 260-261, §5.8.2 eq. (5.79)/(5.80) (strong alternatives for strict convex inequalities)

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.strong_alternatives_strict_convex {n mm p : ℕ}
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ) (hCQ : ∃ x, ∀ j, ⟪a j, x⟫ = b j) :
    (∃ x, (∀ i, fc i x < 0) ∧ ∀ j, ⟪a j, x⟫ = b j) ↔
      ¬∃ (lam : Fin mm → ℝ) (nu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧ lam ≠ 0 ∧
        0 ≤ dualFunction 0 fc a b lam nu := by
  sorry
