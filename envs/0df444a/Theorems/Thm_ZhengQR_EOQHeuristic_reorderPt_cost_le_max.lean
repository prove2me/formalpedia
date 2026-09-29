-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_reorderPt_cost_le_max
-- name    : ZhengQR.EOQHeuristic.reorderPt_cost_le_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:42:04.084727+00:00
-- url     : https://prove2.me/theorems/1138e152-a8a2-4370-a0eb-883cee835b74
-- title:
--   Corollary 1 — $G(r(Q)) \le \max(G(r), G(r + Q))$ for all $Q > 0$ and all $r$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $r(Q)$ be the optimal reorder point for the order quantity $Q$. Then for every $Q > 0$ and every $r \in \mathbb{R}$,
--
--   $$G(r(Q)) \le \max\big(G(r),\, G(r + Q)\big).$$
--
--   The value $G(r(Q))$ is thus the smallest possible maximum of the inventory cost rate over the endpoints of a cycle of length $Q$; it is used to compare the stochastic and the EOQ model in Lemma 7.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Corollary 1

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem reorderPt_cost_le_max {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ∀ Q : ℝ, 0 < Q → ∀ r : ℝ,
      newsvendorCost μ h p (reorderPt (newsvendorCost μ h p) lam K Q) ≤ max (newsvendorCost μ h p r) (newsvendorCost μ h p (r + Q)) := by sorry

end ZhengQR.EOQHeuristic
