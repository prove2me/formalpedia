-- Prove2me | Theorems.Thm_ConvexOptimization_sc_newton_decrement_contraction
-- name    : ConvexOptimization.sc_newton_decrement_contraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:14:34.805603+00:00
-- url     : https://prove2.me/theorems/35f31357-2f52-48fd-8174-34db66fb0949
-- title:
--   Newton-decrement contraction of the pure step
-- statement:
--   **Quadratic contraction of the Newton decrement** — inequality (9.55) of Boyd & Vandenberghe.
--
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and convex, let $f$ be self-concordant on $\Omega$ with positive definite Hessian and with closed sublevel sets $\{y \in \Omega : f(y) \le c\}$. Let $x \in \Omega$, let $\Delta$ solve $\nabla^2 f(x)\Delta = -\nabla f(x)$, and let $\lambda \ge 0$ be the Newton decrement at $x$, $\lambda^2 = \langle \nabla f(x), -\Delta\rangle$. If $\lambda < 1$, then the full Newton step remains in the domain, $x + \Delta \in \Omega$, and the decrement at the new point satisfies
--
--   $$\lambda(x + \Delta) \;\le\; \Bigl(\frac{\lambda}{1 - \lambda}\Bigr)^{2}.$$
--
--   Two things are asserted at once, and both matter. The domain statement is not automatic — for a barrier objective, leaving $\Omega$ means violating a constraint — and self-concordance is precisely what guarantees the unit step is safe once $\lambda < 1$. The contraction then gives quadratic convergence beyond an *absolute* threshold: for $\lambda \le 1/4$, say, the decrement is at most squared at each step, so the number of iterations to reach any accuracy is bounded without reference to problem constants.
--
--   **Formalization Note** The conclusion quantifies over any Newton direction $\Delta'$ and any nonnegative $\lambda'$ with $\lambda'^2 = \langle \nabla f(x+\Delta), -\Delta'\rangle$, rather than asserting uniqueness of the decrement. The closed-sublevel-set hypothesis is the standing assumption of B&V §9.6.4. Source: B&V §9.6.4, p. 505, eq. (9.55) / exercise 9.18; proof in Nesterov, *Lectures on Convex Optimization*, Theorem 5.2.2.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 505, 517, §9.6.4 eq. (9.55) (quadratic contraction of the Newton decrement) and exercise 9.18, p. 517 (quadratic convergence). Proof source: Nesterov 2018, Lectures on Convex Optimization (2nd edition), Springer, Theorem 5.2.2. The closed-sublevel-set hypothesis is the standing assumption of §9.6.4

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.sc_newton_decrement_contraction {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hsc : IsSelfConcordantOn Ω f)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x ∈ Ω, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x ∈ Ω, HasFDerivAt g (H x) x)
    (hHpd : ∀ x ∈ Ω, ∀ v, v ≠ 0 → 0 < ⟪H x v, v⟫)
    (hclosed : ∀ c : ℝ, IsClosed {y | y ∈ Ω ∧ f y ≤ c})
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω)
    (Δ : EuclideanSpace ℝ (Fin n)) (hΔ : H x Δ = -g x)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam : lam ^ 2 = ⟪g x, -Δ⟫) (hlt : lam < 1) :
    x + Δ ∈ Ω ∧
    ∀ (Δ' : EuclideanSpace ℝ (Fin n)) (lam' : ℝ),
      H (x + Δ) Δ' = -g (x + Δ) → 0 ≤ lam' → lam' ^ 2 = ⟪g (x + Δ), -Δ'⟫ →
      lam' ≤ (lam / (1 - lam)) ^ 2 := by
  sorry
