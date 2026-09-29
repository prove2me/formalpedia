-- Prove2me | Theorems.Thm_ConvexOptimization_sc_suboptimality_from_decrement
-- name    : ConvexOptimization.sc_suboptimality_from_decrement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:14:03.371409+00:00
-- url     : https://prove2.me/theorems/5dca5d39-cf04-4c1b-99d8-5f4ec00dab9f
-- title:
--   Suboptimality from the Newton decrement
-- statement:
--   **The Newton decrement bounds suboptimality**, with an absolute constant.
--
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and convex, let $f$ be self-concordant on $\Omega$ with positive definite Hessian throughout, and suppose $f$ attains its minimum on $\Omega$ at $x^{\star} \in \Omega$. For $x \in \Omega$ let $\Delta$ be the Newton direction, i.e. the solution of $\nabla^2 f(x)\Delta = -\nabla f(x)$, and let $\lambda \ge 0$ be the *Newton decrement* at $x$, defined by
--
--   $$\lambda^{2} \;=\; \langle \nabla f(x),\, -\Delta\rangle \;=\; \nabla f(x)^{T}\nabla^2 f(x)^{-1}\nabla f(x).$$
--
--   If $\lambda \le 0.68$, then
--
--   $$f(x) - f(x^{\star}) \;\le\; \lambda^{2}.$$
--
--   The decrement is available for free once the Newton step has been computed, so this inequality is the method's stopping criterion. What distinguishes it from the strongly convex theory is that the constant is absolute: no $m$, $M$ or $L$ appears, and the bound is invariant under affine changes of coordinates, exactly as self-concordance is. The threshold $0.68$ is the book's; the estimate degrades and then fails for larger decrements, where the damped phase is still in force.
--
--   **Formalization Note** The Newton direction is characterized by the linear equation rather than by inverting the Hessian, and the decrement is introduced as a nonnegative real `lam` with `lam ^ 2 = ⟪g x, -Δ⟫`, which avoids a square root. Positive definiteness of the Hessian appears as `∀ v ≠ 0, 0 < ⟪H x v, v⟫`, and membership `x⋆ ∈ Ω` is explicit — the minimum must be attained inside the domain. Source: B&V §9.6.3, p. 502.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 501-502, §9.6.3 eq. (9.50) (the Newton decrement bounds suboptimality: f(x) - p* <= lambda(x)^2 when lambda(x) <= 0.68)

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.sc_suboptimality_from_decrement {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (xstar : EuclideanSpace ℝ (Fin n)) (hxstar : xstar ∈ Ω)
    (hstar : IsMinOn f Ω xstar)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪g x, -Δ⟫)
    (hsmall : lam ≤ 0.68) :
    f x - f xstar ≤ lam ^ 2 := by
  sorry
