-- Prove2me | Theorems.Thm_ConvexOptimization_conic_slater_strong_duality
-- name    : ConvexOptimization.conic_slater_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:03:43.006455+00:00
-- url     : https://prove2.me/theorems/fac0f5ea-819c-4d39-8faf-6ad69189f4e8
-- title:
--   Conic strong duality under generalized Slater
-- statement:
--   **Strong duality for cone programs under a generalized Slater condition.**
--
--   Let $K \subseteq \mathbb{R}^d$ be a closed convex cone with dual cone $K^{*}$, and consider
--
--   $$\text{minimize } f_0(x) \quad\text{subject to}\quad f(x) \preceq_K 0, \quad \langle a_j, x\rangle = b_j \ (j = 1,\dots,p),$$
--
--   where $f_0 : \mathbb{R}^n \to \mathbb{R}$ is convex, $f : \mathbb{R}^n \to \mathbb{R}^d$ is $K$-convex — meaning $\theta f(x) + (1-\theta)f(y) - f(\theta x + (1-\theta)y) \in K$ for $\theta \in [0,1]$ — and $a_1,\dots,a_p$ are linearly independent. Assume the **generalized Slater condition**: some $\tilde{x}$ satisfies the equality constraints and has $-f(\tilde{x})$ in the *interior* of $K$. If the optimal value $p^{\star}$ is finite, then the dual optimum is attained: there exist $z \in K^{*}$ and $\nu \in \mathbb{R}^p$ with
--
--   $$\inf_{x \in \mathbb{R}^n}\Bigl[f_0(x) + \langle z, f(x)\rangle + \sum_{j=1}^{p}\nu_j\bigl(\langle a_j,x\rangle - b_j\bigr)\Bigr] \;=\; p^{\star} .$$
--
--   This is Slater's theorem with the componentwise inequality $f_i(x) \le 0$ replaced by a generalized inequality with respect to $K$, and the multiplier vector $\lambda \succeq 0$ replaced by a dual-cone vector $z \in K^{*}$. Specializing $K$ to the positive semidefinite cone gives semidefinite programming duality and the LMI theorems of alternatives; specializing to the nonnegative orthant recovers the ordinary case.
--
--   **Formalization Note** The cone is given by explicit convexity, closedness and positive-scaling hypotheses rather than by a bundled structure, and $K$-convexity of $f$ is stated as the displayed membership; $p^{\star}$ appears as an `sInf` over the image of the feasible set with an accompanying `BddBelow` hypothesis. Source: B&V §5.9.1–5.9.2, pp. 264–266.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 264-266, §5.9.1-§5.9.2 (Lagrange duality and strong duality for problems with generalized inequalities, under the generalized Slater condition)

import Mathlib
import Definitions.Def_dualCone

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.conic_slater_strong_duality {n d p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x y : EuclideanSpace ℝ (Fin n), ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • f x + (1 - θ) • f y - f (θ • x + (1 - θ) • y) ∈ K)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs_slater : -f xs ∈ interior K)
    (hxs_eq : ∀ j, ⟪a j, xs⟫ = b j)
    (hbdd : BddBelow (f₀ '' {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j})) :
    ∃ (z : EuclideanSpace ℝ (Fin d)) (nu : Fin p → ℝ), z ∈ dualCone K ∧
      (⨅ x : EuclideanSpace ℝ (Fin n),
        ((f₀ x + ⟪z, f x⟫ + ∑ j, nu j * (⟪a j, x⟫ - b j) : ℝ) : EReal)) =
      ((sInf (f₀ '' {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j}) : ℝ) : EReal) := by
  sorry
