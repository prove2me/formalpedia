-- Prove2me | Definitions.Def_ConvexOptimization_lagrangeDuality
-- name    : ConvexOptimization_lagrangeDuality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-12T19:30:37.19842+00:00
-- url     : https://prove2.me/theorems/c755f214-8896-48ec-88c5-ddfb73fde928
-- title:
--   Lagrange duality: feasible set, Lagrangian, and dual function
-- statement:
--   The three objects on which all of Lagrange duality rests, for the standard optimization problem
--
--   $$\text{minimize } f_0(x) \quad \text{subject to } f_i(x) \le 0 \ (i = 1,\dots,m), \quad \langle a_j, x\rangle = b_j \ (j = 1,\dots,p),$$
--
--   with variable $x \in \mathbb{R}^n$, objective $f_0 : \mathbb{R}^n \to \mathbb{R}$, inequality-constraint functions $f_i : \mathbb{R}^n \to \mathbb{R}$, and equality constraints given by vectors $a_j \in \mathbb{R}^n$ and scalars $b_j$. This module defines, in order:
--
--   $$\mathcal{F} = \{x : f_i(x) \le 0 \ \forall i, \ \langle a_j, x\rangle = b_j \ \forall j\}, \qquad L(x,\lambda,\nu) = f_0(x) + \sum_{i=1}^{m} \lambda_i f_i(x) + \sum_{j=1}^{p} \nu_j\bigl(\langle a_j, x\rangle - b_j\bigr), \qquad g(\lambda,\nu) = \inf_{x \in \mathbb{R}^n} L(x, \lambda, \nu).$$
--
--   The *feasible set* $\mathcal{F}$ is the point set cut out by the constraints. The *Lagrangian* $L$ augments the objective with the constraint functions weighted by multipliers $\lambda \in \mathbb{R}^m$ and $\nu \in \mathbb{R}^p$; no sign restriction on $\lambda$ is built in, since the restriction $\lambda \succeq 0$ belongs to the statements that use it. The *dual function* $g$ is the pointwise infimum of $L$ over the *unconstrained* variable $x$, and takes values in the extended reals $\overline{\mathbb{R}} = [-\infty,+\infty]$ because that infimum is $-\infty$ exactly when $L(\cdot,\lambda,\nu)$ is unbounded below.
--
--   These are the interface against which every duality statement of the mission is phrased: weak duality, Slater's strong-duality theorem, the saddle-point characterization, complementary slackness and the KKT conditions. Being concave and independent of any convexity assumption on the data, $g$ furnishes a lower bound on the optimal value for every $\lambda \succeq 0$.
--
--   **Formalization Note** The problem is stated in *total*-function form, i.e. with domain $\mathcal{D} = \mathbb{R}^n$, which avoids carrying a domain around; equality constraints are written as inner products $\langle a_j, x\rangle$ rather than through a matrix. Vectors live in `EuclideanSpace ℝ (Fin n)`. The dual function is `EReal`-valued and defined as an infimum in that complete lattice, so it is always the true greatest lower bound and never a junk value; it is never $+\infty$, since the index type is nonempty.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 127, 215-216, §4.1 eq. (4.1) (standard form problem, whose constraints cut out the feasible set), §5.1.1 (the Lagrangian) and §5.1.2 (the Lagrange dual function); the latter two are displayed unnumbered in the text. Formalized in total-function form, i.e. with domain D = R^n, and with equality constraints written as inner products <a_j, x> = b_j rather than through a matrix

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- Feasible set of the standard problem (B&V (5.1)/(4.1)). -/
def feasibleSet {n mm p : ℕ}
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | (∀ i, fc i x ≤ 0) ∧ ∀ j, ⟪a j, x⟫ = b j}

/-- The Lagrangian `L(x, λ, ν) = f₀ x + Σ λᵢ fᵢ x + Σ νⱼ (⟪aⱼ,x⟫ − bⱼ)`
(B&V §5.1.1). -/
noncomputable def lagrangian {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (lam : Fin mm → ℝ) (nu : Fin p → ℝ) : ℝ :=
  f₀ x + ∑ i, lam i * fc i x + ∑ j, nu j * (⟪a j, x⟫ - b j)

/-- The Lagrange dual function `g(λ, ν) = inf_x L(x, λ, ν)`, valued in `EReal`
since the infimum may be `−∞` (B&V §5.1.2). -/
noncomputable def dualFunction {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (lam : Fin mm → ℝ) (nu : Fin p → ℝ) : EReal :=
  ⨅ x : EuclideanSpace ℝ (Fin n), ((lagrangian f₀ fc a b x lam nu : ℝ) : EReal)

end ConvexOptimization


