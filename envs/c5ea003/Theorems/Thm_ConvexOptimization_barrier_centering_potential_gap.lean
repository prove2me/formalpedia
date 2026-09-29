-- Prove2me | Theorems.Thm_ConvexOptimization_barrier_centering_potential_gap
-- name    : ConvexOptimization.barrier_centering_potential_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:16:22.041428+00:00
-- url     : https://prove2.me/theorems/76c2b2c6-ae8a-4496-9280-0ce713f6864a
-- title:
--   Per-centering potential gap
-- statement:
--   **The objective gap at the start of each centering step is bounded by $m(\mu - 1 - \log\mu)$** — inequalities (11.25)–(11.26) of Boyd & Vandenberghe.
--
--   With the notation above, fix $t > 0$ and $\mu > 1$, and let $x^{\star}(t)$ and $x^{\star}(\mu t)$ be central points for $t$ and $\mu t$ respectively. The barrier method starts the next centering problem, whose objective is $\mu t f_0 + \varphi$, at the previous central point $x^{\star}(t)$. Then
--
--   $$\bigl(\mu t f_0(x^{\star}(t)) + \varphi(x^{\star}(t))\bigr) \;-\; \bigl(\mu t f_0(x^{\star}(\mu t)) + \varphi(x^{\star}(\mu t))\bigr) \;\le\; m\,\bigl(\mu - 1 - \log\mu\bigr).$$
--
--   The initial suboptimality of every centering problem is therefore bounded by a quantity depending only on $m$ and $\mu$ — not on $t$, and not on how far along the path the method has travelled. Feeding it into the Newton iteration bound gives a uniform per-centering cost of $m(\mu - 1 - \log\mu)/\gamma + c$ Newton steps. The trade-off in $\mu$ is now visible: large $\mu$ means few outer steps but expensive centering, and since $\mu - 1 - \log\mu \approx (\mu-1)^2/2$ for $\mu$ near $1$, the choice $\mu = 1 + 1/\sqrt{m}$ makes the per-centering cost $O(1)$ while keeping the outer count $O(\sqrt{m}\log(1/\varepsilon))$ — the balance that produces the mission's goal.
--
--   **Formalization Note** Both central points are hypotheses (strictly feasible minimizers of the respective centering objectives over the strictly feasible set), so the statement asserts nothing about existence of the central path. Source: B&V §11.5.2, pp. 588–589, eqs. (11.25)–(11.26).
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 588-589, §11.5.2 eq. (11.25)-(11.26) (bound on the objective gap at the start of each centering step)

import Mathlib
import Definitions.Def_ConvexOptimization_logBarrier

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.barrier_centering_potential_gap {n mI : ℕ} (t μ : ℝ)
    (ht : 0 < t) (hμ : 1 < μ)
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (hfc_diff : ∀ i, Differentiable ℝ (fc i)) (hf₀_diff : Differentiable ℝ f₀)
    (xc xc' : EuclideanSpace ℝ (Fin n))
    (hxc_str : ∀ i, fc i xc < 0) (hxc'_str : ∀ i, fc i xc' < 0)
    (hxc_min : IsMinOn (fun x => t * f₀ x + logBarrier fc x)
      {x | ∀ i, fc i x < 0} xc)
    (hxc'_min : IsMinOn (fun x => μ * t * f₀ x + logBarrier fc x)
      {x | ∀ i, fc i x < 0} xc') :
    μ * t * f₀ xc + logBarrier fc xc - (μ * t * f₀ xc' + logBarrier fc xc') ≤
      (mI : ℝ) * (μ - 1 - Real.log μ) := by
  sorry
