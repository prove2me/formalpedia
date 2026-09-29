-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_eoqQty_le_optQty
-- name    : ZhengQR.EOQHeuristic.eoqQty_le_optQty
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:47:45.943988+00:00
-- url     : https://prove2.me/theorems/66b7113e-e343-4da1-ae2d-60ef6f5e8850
-- title:
--   Theorem 2 (first inequality) — the EOQ quantity underestimates the optimal order quantity, $Q^*_d \le Q^*$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $Q^*$ be an optimal order quantity of the stochastic model, i.e. $Q^* > 0$ and $C(Q^*) \le C(Q)$ for every $Q > 0$, and let $Q^*_d = \sqrt{2\lambda K(h+p)/(hp)}$ be the EOQ order quantity. Then
--
--   $$Q^*_d \le Q^*.$$
--
--   This is the first inequality of Theorem 2 of the paper, proved on p. 96 from Lemma 6 and Lemma 7: $A(Q^*_d) \le A_d(Q^*_d) = \lambda K = A(Q^*)$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 96, Theorem 2 (first inequality) and its proof

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem eoqQty_le_optQty {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Qs : ℝ)
    (hQs : IsOptQty (newsvendorCost μ h p) lam K Qs) :
    eoqQty lam K h p ≤ Qs := by sorry

end ZhengQR.EOQHeuristic
