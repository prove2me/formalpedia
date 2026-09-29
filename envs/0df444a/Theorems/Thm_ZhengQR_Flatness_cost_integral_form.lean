-- Prove2me | Theorems.Thm_ZhengQR_Flatness_cost_integral_form
-- name    : ZhengQR.Flatness.cost_integral_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:04:37.902748+00:00
-- url     : https://prove2.me/theorems/4b91bae2-4df8-4cee-9db0-5abd898856ad
-- title:
--   Eq. (7): ∫_{r(Q)}^{r(Q)+Q} G = ∫_0^Q H and C(Q) = (λK + ∫_0^Q H(y)dy)/Q
-- statement:
--   In the stochastic $(Q, r)$ model, let $r(Q)$ be an optimal reorder point for the order quantity $Q$, let $H(Q) = G(r(Q))$ for $Q>0$ with $H(0) = G(y^0)$, and let $C(Q) = c(Q, r(Q))$ be the average cost with the reorder point chosen optimally. Then for every $Q>0$,
--
--   $$\int_{r(Q)}^{r(Q)+Q} G(y)\,dy = \int_0^Q H(y)\,dy \qquad\text{and}\qquad C(Q) = \frac{\lambda K + \int_0^Q H(y)\,dy}{Q}.$$
--
--   This rewrites the two-variable cost as a function of the order quantity alone, and is the starting point of every comparison between the stochastic model and the EOQ model.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Eq. (7)

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem cost_integral_form (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in M.r Q..M.r Q + Q, M.G y) = (∫ y in (0 : ℝ)..Q, M.H y) ∧
      M.C Q = (M.lam * M.K + ∫ y in (0 : ℝ)..Q, M.H y) / Q := by sorry

end ZhengQR.Flatness
