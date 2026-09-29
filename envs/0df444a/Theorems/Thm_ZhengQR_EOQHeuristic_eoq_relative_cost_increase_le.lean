-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_eoq_relative_cost_increase_le
-- name    : ZhengQR.EOQHeuristic.eoq_relative_cost_increase_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:48:10.077989+00:00
-- url     : https://prove2.me/theorems/43834915-688e-4d10-a636-ea49ad3f96b6
-- title:
--   Theorem 5 — $R = (C(Q^*_d) - C^*)/C^* \le 1/8 - \frac12(\frac12 - Q^*_d/Q^*)^2 \le 1/8$
-- statement:
--   Consider a single-item continuous-review $(Q, r)$ inventory system with demand rate $\lambda > 0$, leadtime $L > 0$, fixed ordering cost $K > 0$, holding cost rate $h > 0$ and backorder penalty rate $p > 0$. The leadtime demand $D \ge 0$ has mean $E(D) = \lambda L$, and the newsvendor cost $G(y) = E[h(y-D)^+ + p(D-y)^+]$ attains its minimum at a unique point. For an order quantity $Q > 0$ let
--
--   $$C(Q) = \min_r \frac{\lambda K + \int_r^{r+Q} G(y)\,dy}{Q}$$
--
--   be the average cost when the reorder point is chosen optimally for $Q$. Let $Q^*$ be an optimal order quantity, $C^* = C(Q^*)$, and let $Q^*_d = \sqrt{2\lambda K(h+p)/(hp)}$ be the order quantity of the EOQ model with backorders. Then the relative cost increase from using $Q^*_d$ instead of $Q^*$ satisfies
--
--   $$R = \frac{C(Q^*_d) - C^*}{C^*} \;\le\; \frac18 - \frac12\left(\frac12 - \frac{Q^*_d}{Q^*}\right)^2 \;\le\; \frac18 .$$
--
--   Using the deterministic EOQ quantity in the stochastic model, with the reorder point re-optimised for it, therefore never costs more than $12.5\%$ above the optimum, for every leadtime-demand distribution.
--
--   **Formalization Note** $C(Q^*_d)$ is the stochastic cost at the EOQ quantity, with the reorder point chosen optimally for $Q^*_d$ in the stochastic model (not the EOQ model's reorder point). $Q^*$ is any order quantity with $Q^* > 0$ and $C(Q^*) \le C(Q)$ for all $Q > 0$; its existence and uniqueness is the Lemma 6 milestone. No positivity of $C^*$ is assumed: it follows from the model.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 98, Theorem 5 (proof pp. 98–99)

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem eoq_relative_cost_increase_le {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Qs : ℝ)
    (hQs : IsOptQty (newsvendorCost μ h p) lam K Qs) :
    (optCost (newsvendorCost μ h p) lam K (eoqQty lam K h p) - optCost (newsvendorCost μ h p) lam K Qs) / optCost (newsvendorCost μ h p) lam K Qs
        ≤ 1 / 8 - 1 / 2 * (1 / 2 - eoqQty lam K h p / Qs) ^ 2 ∧
      1 / 8 - 1 / 2 * (1 / 2 - eoqQty lam K h p / Qs) ^ 2 ≤ (1 / 8 : ℝ) := by sorry

end ZhengQR.EOQHeuristic
