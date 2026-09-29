-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_eoq_H_and_optQty
-- name    : ZhengQR.OrderQty.eoq_H_and_optQty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:51:36.586715+00:00
-- url     : https://prove2.me/theorems/7fefa2a3-6a17-435d-94e8-4a7b53b58552
-- title:
--   Eqs. (18), (20) — in the EOQ model $H_d(Q) = hpQ/(h + p)$ and $Q^*_d = \sqrt{2\lambda K(h + p)/(hp)}$ is optimal
-- statement:
--   Let $\lambda, L, K, h, p > 0$ and let $G_d(y) = h(y - \lambda L)^+ + p(\lambda L - y)^+$ be the inventory-cost rate of the EOQ model with backorders. Apply the $(Q, r)$ machinery to $G_d$: $r_d(Q)$ is its optimal reorder point, $H_d(Q) = G_d(r_d(Q))$ for $Q > 0$ with $H_d(0) = G_d(y^0_d)$, and $C_d(Q) = c_d(Q, r_d(Q))$. Then:
--
--   1. $G_d$ has its minimum point at $y^0_d = \lambda L$, and $G_d(y^0_d) = 0$;
--   2. for $Q > 0$, $r_d(Q) = \lambda L - \dfrac{h}{h+p}\,Q$;
--   3. for every $Q \ge 0$,
--   $$H_d(Q) = \frac{hp}{h+p}\,Q; \tag{18}$$
--   4. the unique optimal order quantity of the EOQ model is
--   $$Q^*_d = \sqrt{\frac{2\lambda K (h+p)}{hp}}. \tag{20}$$
--
--   These are the classical EOQ-with-backorders formulas, rederived with the optimality conditions of the stochastic model so that both models are measured by the same yardstick.
--
--   **Formalization Note** $y^0_d$ and $r_d(Q)$ are the chosen minimizers of the generic machinery; part 1 and part 2 assert that the choices are the stated points (they are unique). Parts 3 and 4 are the displays (18) and (20).
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 94, Eqs. (18) and (20) (with the displays for y⁰_d and r_d(Q) above (18))

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Eqs. (18) and (20) (Zheng 1992, p. 94): in the EOQ model, whose inventory cost rate is
`G_d(y) = h (y - λL)⁺ + p (λL - y)⁺`, the minimum point is `y⁰_d = λL` with `G_d(y⁰_d) = 0`,
`r_d(Q) = λL - hQ/(h + p)` and `H_d(Q) = G_d(r_d(Q)) = hp/(h + p) Q` for `Q > 0` (and
`H_d(Q) = hp/(h + p) Q` for all `Q ≥ 0`), and `Q*_d = √(2λK(h + p)/(hp))` is the unique optimal
order quantity. -/
theorem eoq_H_and_optQty
    {lam L K h p : ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p) :
    minPoint (eoqCost lam L h p) = lam * L ∧
    eoqCost lam L h p (lam * L) = 0 ∧
    (∀ Q : ℝ, 0 < Q → optReorder (eoqCost lam L h p) Q = lam * L - h / (h + p) * Q) ∧
    (∀ Q : ℝ, 0 ≤ Q → Hfun (eoqCost lam L h p) Q = h * p / (h + p) * Q) ∧
    IsOptQty (eoqCost lam L h p) lam K (eoqQty lam K h p) ∧
    ∀ Q : ℝ, IsOptQty (eoqCost lam L h p) lam K Q → Q = eoqQty lam K h p := by sorry

end ZhengQR.OrderQty
