-- Prove2me | Theorems.Thm_ZhengQR_Flatness_cost_flatter_than_eoq
-- name    : ZhengQR.Flatness.cost_flatter_than_eoq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T02:09:10.468693+00:00
-- url     : https://prove2.me/theorems/210f5244-78cc-42a6-b777-24518bfd8549
-- title:
--   Theorem 4: C(αQ*)/C* ≤ ½(α + 1/α) for all α > 0
-- statement:
--   Consider the stochastic continuous-review $(Q, r)$ inventory model with demand rate $\lambda>0$, leadtime $L>0$, fixed ordering cost $K>0$, holding and backorder cost rates $h, p>0$, and a nonnegative leadtime demand $D$ with finite mean $E(D) = \lambda L$ whose inventory cost rate $G(y) = E[h(y-D)^+ + p(D-y)^+]$ has a unique minimizer. Let $C(Q) = \min_r c(Q, r)$ be the average cost of the order quantity $Q$ with the reorder point re-optimized for $Q$, let $Q^*$ be an optimal order quantity and $C^* = C(Q^*)$. Then
--
--   $$\frac{C(\alpha Q^*)}{C^*} \le \frac{1}{2}\left(\alpha + \frac{1}{\alpha}\right) \qquad \forall \alpha>0.$$
--
--   In the EOQ model the relative cost of a scaled order quantity equals $\frac12(\alpha + 1/\alpha)$ exactly (Eq. (25)), a function that is already very flat around $\alpha = 1$; the theorem shows that the stochastic $(Q,r)$ cost is even flatter, so a misestimated order quantity costs relatively less in the stochastic system than in the EOQ.
--
--   **Formalization Note** $C(\alpha Q^*)$ is $c(\alpha Q^*, r(\alpha Q^*))$: the reorder point is chosen optimally for the scaled quantity, not held at $r(Q^*)$. The theorem holds for every optimal $Q^*$; existence of one is part of the milestone for Eq. (8). $C^*>0$ is a consequence of the model, not a hypothesis.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 97, Theorem 4 (proof p. 98)

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem cost_flatter_than_eoq (M : QRModel) (Qs : ℝ) (hQs : M.IsOptQty Qs)
    (α : ℝ) (hα : 0 < α) :
    M.C (α * Qs) / M.C Qs ≤ 1 / 2 * (α + 1 / α) := by sorry

end ZhengQR.Flatness
