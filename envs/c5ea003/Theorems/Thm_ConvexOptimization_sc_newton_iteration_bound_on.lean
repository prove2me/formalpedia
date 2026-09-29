-- Prove2me | Theorems.Thm_ConvexOptimization_sc_newton_iteration_bound_on
-- name    : ConvexOptimization.sc_newton_iteration_bound_on
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-17T01:43:29.76836+00:00
-- url     : https://prove2.me/theorems/2607cd4e-a554-4b45-b3cb-cb9731d504bc
-- title:
--   Newton complexity for self-concordant functions
-- statement:
--   **The Newton iteration bound for self-concordant functions, with absolute constants** — inequality (9.56) of Boyd & Vandenberghe, with the line search confined to the domain.
--
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and convex, let $f$ be self-concordant on $\Omega$ with positive definite Hessian, attaining its minimum at $x^{\star} \in \Omega$, and with all sublevel sets $\{x \in \Omega : f(x) \le c\}$ closed. Fix backtracking parameters $\alpha \in (0,1/2)$, $\beta \in (0,1)$, an accuracy $\varepsilon \in (0,1/4)$, and a starting point $x^{(0)} \in \Omega$. Then there is a damped Newton run with backtracking on $\Omega$ starting at $x^{(0)}$, and an index $K$ with
--
--   $$K \;\le\; \frac{20 - 8\alpha}{\alpha\beta(1-2\alpha)^{2}}\,\bigl(f(x^{(0)}) - f(x^{\star})\bigr) \;+\; \log_2\log_2(1/\varepsilon) \;+\; 1, \qquad f(x^{(K)}) - f(x^{\star}) \le \varepsilon .$$
--
--   The shape is the familiar two phases — a damped phase of fixed decrease $\gamma = \alpha\beta(1-2\alpha)^2/(20-8\alpha)$ per step, then a doubly logarithmic quadratic phase — but every constant is *absolute*. Nothing in the bound refers to the dimension $n$, to strong-convexity or smoothness moduli, or to a Lipschitz constant for the Hessian, and nothing changes under an affine change of coordinates. That is the whole payoff of self-concordance, and it is what makes a per-centering bound uniform along the central path in the barrier method.
--
--   **Formalization note.** The run is governed by `IsDampedNewtonRunOn`, whose line search `IsBacktrackingStepOn` accepts the largest step $\beta^{j}$ whose trial point is **both** in $\Omega$ and Armijo-acceptable. This is what B&V's convention "$f = +\infty$ off $\operatorname{dom} f$" (§9.1) delivers automatically: an infeasible trial point cannot satisfy the Armijo inequality. For a real-valued $f$ it has to be said explicitly, because the hypotheses constrain $f$ only on $\Omega$ — the earlier formalization `ConvexOptimization.sc_newton_iteration_bound`, which used the unconfined line search, is false for exactly this reason and has been disproved. The sublevel-set hypothesis is likewise stated at every level $c$ (not only at $f(x^{(0)})$), matching the Dikin-ellipsoid argument behind (9.55). Otherwise the statement is unchanged, and $1/\gamma = (20-8\alpha)/(\alpha\beta(1-2\alpha)^2)$ as in the book.
--
--   The statement is existential in the run and the index — "some faithful run succeeds" — matching the book's idealized analysis.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 503-505, §9.6.4 eq. (9.56) (Newton iteration bound for self-concordant functions), with the line search read under the convention of §9.1, p. 457.

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_ConvexOptimization_IsDampedNewtonRunOn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.sc_newton_iteration_bound_on {n : ℕ} (α β ε : ℝ)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 4)
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
    (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (hclosed : ∀ c : ℝ, IsClosed {x | x ∈ Ω ∧ f x ≤ c}) :
    ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (K : ℕ),
      x 0 = x0 ∧ IsDampedNewtonRunOn Ω f g H α β x ∧
      (K : ℝ) ≤ (20 - 8 * α) / (α * β * (1 - 2 * α) ^ 2) * (f x0 - f xstar) +
        Real.logb 2 (Real.logb 2 (1 / ε)) + 1 ∧
      f (x K) - f xstar ≤ ε := by
  sorry
