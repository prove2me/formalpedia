-- Prove2me | Theorems.Thm_ConvexOptimization_newton_two_phase_iteration_bound
-- name    : ConvexOptimization.newton_two_phase_iteration_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T15:29:21.537539+00:00
-- url     : https://prove2.me/theorems/b8013d00-4ed9-416d-8c63-227fecefbdbb
-- title:
--   Two-phase Newton complexity bound
-- statement:
--   **The two-phase complexity bound for Newton's method with backtracking** — inequality (9.36) of Boyd & Vandenberghe, the goal of this mission.
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice differentiable with gradient field $\nabla f$ and Hessian field $\nabla^2 f$, and assume, for constants $0 < m \le M$ and $L > 0$,
--
--   $$m I \preceq \nabla^2 f(x) \preceq M I \quad (x \in \mathbb{R}^n), \qquad \lVert \nabla^2 f(x) - \nabla^2 f(y)\rVert \le L \lVert x - y\rVert_2 \quad (x, y \in \mathbb{R}^n).$$
--
--   Let $x^{\star}$ be a global minimizer, $p^{\star} = f(x^{\star})$, fix backtracking parameters $\alpha \in (0,1/2)$, $\beta \in (0,1)$, and let $(x_k)$ be any damped Newton sequence with backtracking. Put
--
--   $$\eta = \min\{1,\,3(1-2\alpha)\}\frac{m^{2}}{L}, \qquad \gamma = \frac{\alpha\beta\eta^{2}m}{M^{2}}, \qquad \varepsilon_0 = \frac{2m^{3}}{L^{2}} .$$
--
--   Then for every accuracy $\varepsilon$ with $0 < \varepsilon \le \varepsilon_0/4$ and every $K \in \mathbb{N}$ satisfying
--
--   $$K \;\ge\; \frac{f(x_0) - p^{\star}}{\gamma} \;+\; \log_2\log_2\bigl(\varepsilon_0/\varepsilon\bigr),$$
--
--   the iterate $x_K$ is $\varepsilon$-optimal:
--
--   $$f(x_K) - p^{\star} \;\le\; \varepsilon .$$
--
--   The two summands are the two phases: at most $(f(x_0) - p^{\star})/\gamma$ damped iterations, each buying a fixed decrease $\gamma$, followed by a quadratically convergent phase whose length grows like $\log_2\log_2(1/\varepsilon)$ — six iterations already give $\varepsilon \approx 5\cdot 10^{-20}\varepsilon_0$. The bound is dimension-free, and its dependence on the accuracy is doubly logarithmic rather than logarithmic, which is the precise sense in which Newton's method outperforms every first-order method.
--
--   **Formalization Note** The hypothesis $\varepsilon \le \varepsilon_0/4$ is stated as `ε ≤ m ^ 3 / (2 * L ^ 2)`; it is needed because the book's count is valid once the quadratic phase has genuinely begun, and for $\varepsilon \in (\varepsilon_0/4, \varepsilon_0)$ the literal bound (9.36) fails. The quantities $\eta$ and $\gamma$ are inlined into the hypothesis on $K$ rather than introduced as abbreviations, and $\log_2$ is Mathlib's `Real.logb 2`. The iterates are governed by the mission's damped-Newton predicate, so the conclusion holds for every faithful run. Source: B&V §9.5.3, p. 491, eq. (9.36).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 491, §9.5.3 eq. (9.36) (total complexity of Newton's method with backtracking: (f(x0) - p*)/gamma + log2 log2(eps0/eps)). Formalized with the extra hypothesis eps <= eps0/4 = m^3/(2 L^2), without which the printed double-log budget fails for eps in (eps0/4, eps0)

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep
import Definitions.Def_ConvexOptimization_IsDampedNewtonSequence

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.newton_two_phase_iteration_bound {n : ℕ} (m M L α β ε : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hL : 0 < L)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hε0 : 0 < ε) (hεsmall : ε ≤ m ^ 3 / (2 * L ^ 2))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHm : ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫)
    (hHM : ∀ x v, ⟪H x v, v⟫ ≤ M * ‖v‖ ^ 2)
    (hHL : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hnewton : IsDampedNewtonSequence f g H α β x)
    (K : ℕ)
    (hK : (f (x 0) - f xstar) /
        (α * β * (min 1 (3 * (1 - 2 * α)) * m ^ 2 / L) ^ 2 * m / M ^ 2) +
        Real.logb 2 (Real.logb 2 (2 * m ^ 3 / L ^ 2 / ε)) ≤ (K : ℝ)) :
    f (x K) - f xstar ≤ ε := by
  sorry
