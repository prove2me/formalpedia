-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_optQty_iff
-- name    : ZhengQR.EOQHeuristic.optQty_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:44:11.75349+00:00
-- url     : https://prove2.me/theorems/dcd7ac99-fb29-4b66-bd9e-131258a74f52
-- title:
--   Eq. (8) — $Q > 0$ is an optimal order quantity iff $H(Q) = C(Q)$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $H(Q) = G(r(Q))$ and $C(Q) = c(Q, r(Q))$. For every $Q > 0$,
--
--   $$Q \text{ is an optimal order quantity} \iff H(Q) = C(Q). \qquad (8)$$
--
--   Here "optimal" means $C(Q) \le C(Q')$ for every $Q' > 0$. The paper derives (8) as the first-order condition $C'(Q^*) = 0$, "the necessary and sufficient condition for optimality".
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 92, Eq. (8)

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem optQty_iff {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    IsOptQty (newsvendorCost μ h p) lam K Q ↔ hFun (newsvendorCost μ h p) lam K Q = optCost (newsvendorCost μ h p) lam K Q := by sorry

end ZhengQR.EOQHeuristic
