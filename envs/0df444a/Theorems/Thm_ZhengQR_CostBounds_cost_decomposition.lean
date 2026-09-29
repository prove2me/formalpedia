-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_cost_decomposition
-- name    : ZhengQR.CostBounds.cost_decomposition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:59:17.731365+00:00
-- url     : https://prove2.me/theorems/fe0f4cbf-5871-4c6f-b545-6601f0d1f965
-- title:
--   Eqs. (13)–(15): $C(Q) = G(y^0) + C_0(Q)$, and $H_0(Q^*) = C_0(Q^*)$ at the optimum
-- statement:
--   In the stochastic $(Q,r)$ model, let $y^0$ be the unique minimizer of $G$, $H_0(Q)=H(Q)-G(y^0)$ and $C_0(Q)=\big(\lambda K+\int_0^Q H_0(y)\,dy\big)/Q$.
--
--   1. For every $Q>0$ the cost splits into the newsboy cost and the controllable cost:
--   $$C(Q)=G(y^0)+C_0(Q).$$
--   2. At every optimal order quantity $Q^*$,
--   $$H_0(Q^*)=C_0(Q^*).$$
--
--   The constant $G(y^0)$ is the part of the inventory cost caused by demand randomness and not controllable through the order quantity; $C_0$ is what the choice of $Q$ trades off.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, pp. 92–93, Eqs. (13), (14), (15)

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem cost_decomposition (M : QRModel) :
    (∀ Q : ℝ, 0 < Q →
      Cfun M.G M.lam M.K Q = M.G (idealPt M.G) + C0fun M.G M.lam M.K Q) ∧
    (∀ Qs : ℝ, IsOptQty M.G M.lam M.K Qs →
      H0fun M.G M.lam M.K Qs = C0fun M.G M.lam M.K Qs) := by sorry

end ZhengQR.CostBounds
