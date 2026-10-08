-- Prove2me | Theorems.Thm_ZhengQR_Flatness_optQty_exists_iff
-- name    : ZhengQR.Flatness.optQty_exists_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:06:21.805375+00:00
-- url     : https://prove2.me/theorems/a147108e-9dad-4ad1-81de-29547d3eef7d
-- title:
--   Eq. (8): an optimal order quantity Q* exists, and Q > 0 is optimal iff H(Q) = C(Q)
-- statement:
--   In the stochastic $(Q, r)$ model, let $C(Q)$ be the average cost of the order quantity $Q$ with the reorder point chosen optimally, and $H(Q) = G(r(Q))$. Call $Q$ an **optimal order quantity** if $Q>0$ and $C(Q)\le C(Q')$ for all $Q'>0$. Then an optimal order quantity $Q^*$ exists, and for every $Q>0$,
--
--   $$Q \text{ is optimal} \iff H(Q) = C(Q).$$
--
--   In particular $H(Q^*) = C(Q^*)$: at the optimum the average cost equals the inventory cost rate at the ends of a replenishment cycle.
--
--   **Formalization Note** The paper opens the paragraph with "Let $Q^*$ be the optimal order quantity", taking its existence for granted; existence is stated here as the first conjunct so that statements about an arbitrary optimal $Q^*$ are not vacuous. The paper derives the condition from the convexity of $C$ (Lemma 5) and the first-order condition $C'(Q)=0$; the statement here is the resulting equivalence, with no differentiability assumed.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 92, Eq. (8)

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem optQty_exists_iff (M : QRModel) :
    (∃ Q : ℝ, M.IsOptQty Q) ∧ ∀ Q : ℝ, 0 < Q → (M.IsOptQty Q ↔ M.H Q = M.C Q) := by sorry

end ZhengQR.Flatness
