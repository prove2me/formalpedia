-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_reorderPt_props
-- name    : ZhengQR.EOQHeuristic.reorderPt_props
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:41:30.772124+00:00
-- url     : https://prove2.me/theorems/247a58c8-9c3b-4e84-94b9-5cc94519db67
-- title:
--   Lemma 3 — $r(Q)$ is independent of $K$, $r(Q) < y^0 < r(Q) + Q$, $r$ decreases, $r + Q$ increases, both diverge
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with fixed ordering cost $K > 0$), let $r(Q)$ be the optimal reorder point for the order quantity $Q$ and $y^0$ the unique minimiser of $G$. Then:
--
--   1. $r(Q)$ does not depend on $K$: for every $Q > 0$ and every $K' > 0$, the optimal reorder point computed with $K'$ equals the one computed with $K$;
--   2. for every $Q > 0$, $\; r(Q) < y^0 < r(Q) + Q$;
--   3. for $0 < Q < Q'$, $\; r(Q') < r(Q)$ and $r(Q) + Q < r(Q') + Q'$, i.e. $r(Q)$ is strictly decreasing and $r(Q) + Q$ is strictly increasing;
--   4. $$\lim_{Q\to\infty} r(Q) = -\infty, \qquad \lim_{Q\to\infty} \big(r(Q) + Q\big) = +\infty.$$
--
--   These properties describe how the optimal replenishment cycle $[r(Q), r(Q)+Q]$ spreads around the ideal position $y^0$ as $Q$ grows.
--
--   **Formalization Note** The paper's part 3 also states $-1 < r'(Q) < 0$. Without a density of the leadtime demand (e.g. Poisson demand) $r$ need not be differentiable, so the derivative clause is omitted and part 3 is stated in the difference form "decreasing / increasing", read as strict (which is what $-1 < r' < 0$ gives). Part 1 is a genuine statement here because $r(Q)$ is defined as a minimiser of $c(Q,\cdot)$, whose formula contains $\lambda K$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 90, Lemma 3

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem reorderPt_props {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    (∀ Q : ℝ, 0 < Q → ∀ K' : ℝ, 0 < K' →
        reorderPt (newsvendorCost μ h p) lam K Q = reorderPt (newsvendorCost μ h p) lam K' Q) ∧
    (∀ Q : ℝ, 0 < Q →
        reorderPt (newsvendorCost μ h p) lam K Q < minPt (newsvendorCost μ h p) ∧ minPt (newsvendorCost μ h p) < reorderPt (newsvendorCost μ h p) lam K Q + Q) ∧
    (∀ Q Q' : ℝ, 0 < Q → Q < Q' →
        reorderPt (newsvendorCost μ h p) lam K Q' < reorderPt (newsvendorCost μ h p) lam K Q ∧ reorderPt (newsvendorCost μ h p) lam K Q + Q < reorderPt (newsvendorCost μ h p) lam K Q' + Q') ∧
    Tendsto (reorderPt (newsvendorCost μ h p) lam K) atTop atBot ∧
    Tendsto (fun Q : ℝ => reorderPt (newsvendorCost μ h p) lam K Q + Q) atTop atTop := by sorry

end ZhengQR.EOQHeuristic
