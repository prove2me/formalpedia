-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_eoq_model_solution
-- name    : ZhengQR.EOQHeuristic.eoq_model_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:45:53.284658+00:00
-- url     : https://prove2.me/theorems/dfce1737-6d40-401e-a5a7-ab6a6800bc6f
-- title:
--   Eqs. (18), (20) — the EOQ model: $r_d(Q) = \lambda L - hQ/(h + p)$, $H_d(Q) = hpQ/(h + p)$, $Q^*_d = \sqrt{2\lambda K(h + p)/(hp)}$
-- statement:
--   Let $\lambda, L, K, h, p > 0$ and consider the deterministic (EOQ) model, whose inventory-cost rate is $G_d(y) = h(y - \lambda L)^+ + p(\lambda L - y)^+$. Apply the general machinery of the mission to $G_d$: $c_d(Q, r) = (\lambda K + \int_r^{r+Q} G_d)/Q$, $r_d(Q)$ the optimal reorder point, $H_d$, $C_d$ and the optimal order quantity. Then
--
--   1. for every $Q > 0$, $\; r_d(Q) = \lambda L - \dfrac{h}{h+p}\,Q$;
--   2. for every $Q \ge 0$,
--   $$H_d(Q) = G_d(r_d(Q)) = \frac{hp}{h+p}\,Q; \qquad (18)$$
--   3. the EOQ model has exactly one optimal order quantity, namely
--   $$Q^*_d = \sqrt{\frac{2\lambda K(h+p)}{hp}}. \qquad (20)$$
--
--   This recovers the classical EOQ formula with backorders from the optimality conditions of the general model, which is what makes the two models directly comparable.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 94, r_d(Q), Eqs. (18) and (20)

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem eoq_model_solution {lam L K h p : ℝ} (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K)
    (hh : 0 < h) (hp : 0 < p) :
    (∀ Q : ℝ, 0 < Q → reorderPt (eoqCost lam L h p) lam K Q = lam * L - h / (h + p) * Q) ∧
    (∀ Q : ℝ, 0 ≤ Q → hFun (eoqCost lam L h p) lam K Q = h * p / (h + p) * Q) ∧
    (∀ Q : ℝ, IsOptQty (eoqCost lam L h p) lam K Q ↔ Q = eoqQty lam K h p) := by sorry

end ZhengQR.EOQHeuristic
