-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_hFun_sandwich
-- name    : ZhengQR.EOQHeuristic.hFun_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:46:55.311985+00:00
-- url     : https://prove2.me/theorems/e246a478-e032-47b9-aaee-87cdaafb89de
-- title:
--   Lemma 7 — $H_0(Q) \le H_d(Q) \le H(Q)$ and $A(Q) \le A_d(Q)$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $H$, $H_0 = H - G(y^0)$ and $A$ be the curves of the stochastic model and $H_d$, $A_d$ those of the EOQ model (the same definitions applied to $G_d$). Then for every $Q \ge 0$,
--
--   $$H_0(Q) \le H_d(Q) \le H(Q), \qquad A(Q) \le A_d(Q).$$
--
--   For a given order quantity, the inventory costs of the stochastic model exceed those of the EOQ model, while their controllable part $H_0$ is smaller.
--
--   **Formalization Note** The paper writes no range for $Q$; the statement is given for $Q \ge 0$, where $H_0(0) = H_d(0) = 0$ and $A(0) = A_d(0) = 0$, as the proof uses.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 95, Lemma 7

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem hFun_sandwich {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 ≤ Q) :
    h0Fun (newsvendorCost μ h p) lam K Q ≤ hFun (eoqCost lam L h p) lam K Q ∧
    hFun (eoqCost lam L h p) lam K Q ≤ hFun (newsvendorCost μ h p) lam K Q ∧
    aFun (newsvendorCost μ h p) lam K Q ≤ aFun (eoqCost lam L h p) lam K Q := by sorry

end ZhengQR.EOQHeuristic
