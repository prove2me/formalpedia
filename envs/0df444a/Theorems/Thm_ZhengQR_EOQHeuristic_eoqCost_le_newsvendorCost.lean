-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_eoqCost_le_newsvendorCost
-- name    : ZhengQR.EOQHeuristic.eoqCost_le_newsvendorCost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:46:27.690641+00:00
-- url     : https://prove2.me/theorems/4681f87a-86cc-469c-a763-2bd4a10c705e
-- title:
--   Eq. (22) — $G_d(y) \le G(y)$ for all $y$ (Jensen)
-- statement:
--   In the stochastic $(Q, r)$ model (demand rate $\lambda > 0$, leadtime $L > 0$, cost rates $h, p > 0$, leadtime demand $D \ge 0$ with $E(D) = \lambda L$, newsvendor cost $G$ with a unique minimiser), the EOQ inventory-cost rate is a lower bound for the stochastic one:
--
--   $$G_d(y) = h(y - \lambda L)^+ + p(\lambda L - y)^+ \;\le\; G(y) = E\big[h(y-D)^+ + p(D-y)^+\big] \qquad \forall y. \qquad (22)$$
--
--   The inventory costs computed in the deterministic model therefore underestimate the actual ones when demand is random.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 94, Eq. (22)

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem eoqCost_le_newsvendorCost {lam L h p : ℝ} {μ : Measure ℝ}
    (hM : IsQRModel lam L h p μ) :
    ∀ y : ℝ, eoqCost lam L h p y ≤ newsvendorCost μ h p y := by sorry

end ZhengQR.EOQHeuristic
