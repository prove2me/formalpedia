-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_eoq_optimum
-- name    : ZhengQR.CostBounds.eoq_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T02:00:47.746934+00:00
-- url     : https://prove2.me/theorems/7b38ee94-c543-450c-a905-cda3b073e4bc
-- title:
--   Eqs. (18), (20): $H_d(Q) = \frac{hp}{h+p}Q$ and $Q^*_d = \sqrt{2\lambda K(h+p)/(hp)}$ is the EOQ optimum
-- statement:
--   Apply the §2 machinery to the deterministic (EOQ) model, whose inventory cost rate is $G_d(y)=h(y-\lambda L)^+ + p(\lambda L-y)^+$, and write $H_d$, $C_d$ for the resulting functions. Then:
--
--   1. For every $Q\ge0$,
--   $$H_d(Q)=\frac{hp}{h+p}\,Q.\qquad(18)$$
--   2. The unique optimal order quantity of the EOQ model is
--   $$Q^*_d=\sqrt{\frac{2\lambda K(h+p)}{hp}}.\qquad(20)$$
--   3. At it, $C_d(Q^*_d)=H_d(Q^*_d)$ (Eq. (8) for the EOQ model).
--
--   This identifies the optimal EOQ cost $C^*_d=C_d(Q^*_d)$ used in Theorem 3.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 94, Eqs. (18) and (20)

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem eoq_optimum (M : QRModel) :
    (∀ Q : ℝ, 0 ≤ Q → Hfun M.Gd M.lam M.K Q = M.h * M.p / (M.h + M.p) * Q) ∧
    (∀ Q : ℝ, IsOptQty M.Gd M.lam M.K Q ↔ Q = M.Qd) ∧
    Cfun M.Gd M.lam M.K M.Qd = Hfun M.Gd M.lam M.K M.Qd := by sorry

end ZhengQR.CostBounds
