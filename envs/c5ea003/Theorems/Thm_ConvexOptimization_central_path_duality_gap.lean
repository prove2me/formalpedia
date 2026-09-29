-- Prove2me | Theorems.Thm_ConvexOptimization_central_path_duality_gap
-- name    : ConvexOptimization.central_path_duality_gap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:15:55.00775+00:00
-- url     : https://prove2.me/theorems/20318a2b-f1d9-431e-88ad-7229c4083977
-- title:
--   Central-path duality gap $m/t$
-- statement:
--   **The central path has duality gap $m/t$.**
--
--   Consider minimizing a convex differentiable $f_0$ subject to $f_i(x) \le 0$ $(i = 1,\dots,m)$, with each $f_i$ convex and differentiable, and let $\varphi(x) = -\sum_i \log(-f_i(x))$ be the logarithmic barrier on the strictly feasible set. Fix $t > 0$ and let $x^{\star}(t)$ be a strictly feasible minimizer of $t f_0 + \varphi$ — the *central point* for the parameter $t$. Then for every feasible $x$,
--
--   $$f_0\bigl(x^{\star}(t)\bigr) - \frac{m}{t} \;\le\; f_0(x),$$
--
--   i.e. $x^{\star}(t)$ is at most $m/t$-suboptimal.
--
--   The bound comes from reading the stationarity condition of the centering problem as a dual feasible point: the multipliers $\lambda_i = -1/(t f_i(x^{\star}(t)))$ are dual feasible and yield exactly the gap $m/t$. Its consequences organize the whole method: to reach accuracy $\varepsilon$ it suffices to follow the path to $t = m/\varepsilon$, and since the outer loop multiplies $t$ by $\mu$ each round, the number of centering steps is logarithmic in $m/(t^{(0)}\varepsilon)$.
--
--   **Formalization Note** The central point is given as a hypothesis — a strictly feasible point minimizing $t f_0 + \varphi$ over `{x | ∀ i, fc i x < 0}` — rather than constructed, so no existence or uniqueness argument is packed into the statement; $m$ appears as the cast `(mI : ℝ)` of the number of inequality constraints. Source: B&V §11.2.2, p. 566.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 566, §11.2.2 (the central point x*(t) is no more than m/t suboptimal; stated unnumbered in the text)

import Mathlib
import Definitions.Def_ConvexOptimization_logBarrier

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.central_path_duality_gap {n mI : ℕ} (t : ℝ) (ht : 0 < t)
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (fc : Fin mI → EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ∀ i, ConvexOn ℝ Set.univ (fc i))
    (hfc_diff : ∀ i, Differentiable ℝ (fc i)) (hf₀_diff : Differentiable ℝ f₀)
    (xc : EuclideanSpace ℝ (Fin n)) (hxc_str : ∀ i, fc i xc < 0)
    (hxc_min : IsMinOn (fun x => t * f₀ x + logBarrier fc x)
      {x | ∀ i, fc i x < 0} xc)
    (x : EuclideanSpace ℝ (Fin n)) (hx : ∀ i, fc i x ≤ 0) :
    f₀ xc - (mI : ℝ) / t ≤ f₀ x := by
  sorry
