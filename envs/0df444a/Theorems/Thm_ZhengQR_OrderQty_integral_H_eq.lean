-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_integral_H_eq
-- name    : ZhengQR.OrderQty.integral_H_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:49:59.573296+00:00
-- url     : https://prove2.me/theorems/19934b64-77fd-4317-80cc-9dd627f15367
-- title:
--   Eq. (7) — $\int_{r(Q)}^{r(Q)+Q} G = \int_0^Q H$ and $C(Q) = (\lambda K + \int_0^Q H(y)dy)/Q$
-- statement:
--   Under the standing assumptions of the model ($\lambda, L, K, h, p > 0$; the leadtime demand distribution $\mu$ is a probability measure, integrable, with mean $\lambda L$ and nonnegative support; $G(y) = \mathbb{E}[h(y-D)^+ + p(D-y)^+]$ has a unique minimizer $y^0$), let $r(Q)$ be the optimal reorder point for $Q$, $H(Q) = G(r(Q))$ for $Q > 0$ with $H(0) = G(y^0)$, and $C(Q) = c(Q, r(Q))$.
--
--   Then for every $Q > 0$,
--
--   $$\int_{r(Q)}^{r(Q)+Q} G(y)\,dy = \int_0^Q H(y)\,dy, \qquad C(Q) = \frac{\lambda K + \int_0^Q H(y)\,dy}{Q}.$$
--
--   This expresses the optimal cost for a given order quantity through the single-variable function $H$, which reduces the two-dimensional optimization over $(Q, r)$ to a one-dimensional one over $Q$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Eq. (7)

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Eq. (7) (Zheng 1992, p. 91): for `Q > 0`, `∫_{r(Q)}^{r(Q)+Q} G = ∫_0^Q H`, and hence
`C(Q) = (λK + ∫_0^Q H(y) dy) / Q`. -/
theorem integral_H_eq
    {lam L K h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 < Q) :
    (∫ y in optReorder (newsvendorCost h p μ) Q..optReorder (newsvendorCost h p μ) Q + Q,
        newsvendorCost h p μ y) =
      (∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y) ∧
    optCost (newsvendorCost h p μ) lam K Q =
      (lam * K + ∫ y in (0 : ℝ)..Q, Hfun (newsvendorCost h p μ) y) / Q := by sorry

end ZhengQR.OrderQty
