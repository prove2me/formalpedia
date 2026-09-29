-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_eoq_invcost_le
-- name    : ZhengQR.CostBounds.eoq_invcost_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:01:45.114211+00:00
-- url     : https://prove2.me/theorems/09b14abb-7417-432c-92b2-ab72000282b5
-- title:
--   Eq. (22): $G_d(y) \le G(y)$ for all $y$
-- statement:
--   In the stochastic $(Q,r)$ model with leadtime demand $D$, $E(D)=\lambda L$, the deterministic inventory cost rate never exceeds the stochastic one:
--   $$G_d(y)\le G(y)\qquad\forall y\in\mathbb R.$$
--
--   The inventory costs computed in the EOQ model therefore underevaluate the actual inventory costs under random demand; combined with Eq. (1) this gives $C_d\le C$ pointwise.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 94, Eq. (22)

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem eoq_invcost_le (M : QRModel) : ∀ y : ℝ, M.Gd y ≤ M.G y := by sorry

end ZhengQR.CostBounds
