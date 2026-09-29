-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_cost_integral_form
-- name    : ZhengQR.CostBounds.cost_integral_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:56:20.941121+00:00
-- url     : https://prove2.me/theorems/995fe380-e6f0-4c08-bcbf-6c6337e43f77
-- title:
--   Eq. (7): $\int_{r(Q)}^{r(Q)+Q}G = \int_0^Q H$ and $C(Q) = (\lambda K + \int_0^Q H)/Q$
-- statement:
--   In the stochastic $(Q,r)$ model, let $r(Q)$ be the optimal reorder point for order quantity $Q$, $H(Q)=G(r(Q))$ with $H(0)=G(y^0)$, and $C(Q)=c(Q,r(Q))$. For every $Q>0$,
--   $$\int_{r(Q)}^{r(Q)+Q}G(y)\,dy=\int_0^Q H(y)\,dy\qquad\text{and}\qquad C(Q)=\frac{\lambda K+\int_0^Q H(y)\,dy}{Q}.$$
--
--   This rewrites the optimal-reorder cost as a function of $Q$ alone, through the single-variable function $H$; every later result on the order quantity starts from this form.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Eq. (7)

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem cost_integral_form (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in reorderPt M.G M.lam M.K Q..reorderPt M.G M.lam M.K Q + Q, M.G y)
        = ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y ∧
      Cfun M.G M.lam M.K Q = (M.lam * M.K + ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y) / Q := by sorry

end ZhengQR.CostBounds
