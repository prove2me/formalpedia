-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_reorder_opt_iff
-- name    : ZhengQR.OrderQty.reorder_opt_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:49:35.128985+00:00
-- url     : https://prove2.me/theorems/f099db5d-70f2-4cda-9090-f7a3b498db73
-- title:
--   Lemma 2 — for $Q > 0$, $r$ is an optimal reorder point iff $G(r) = G(r + Q)$
-- statement:
--   Let $\lambda, L, K, h, p > 0$, let the leadtime demand $D$ have an admissible distribution $\mu$ (probability measure, integrable, mean $\lambda L$, nonnegative), and let $G(y) = \mathbb{E}[h(y-D)^+ + p(D-y)^+]$ attain its minimum at a unique point $y^0$. Let $c(Q, r) = (\lambda K + \int_r^{r+Q} G(y)\,dy)/Q$ be the average cost of Eq. (1).
--
--   Then for every $Q > 0$:
--
--   1. the chosen reorder point $r(Q)$ minimizes $c(Q, \cdot)$ over $\mathbb{R}$, and
--   2. for every $r \in \mathbb{R}$,
--   $$r \text{ minimizes } c(Q, \cdot) \iff G(r) = G(r + Q).$$
--
--   The optimal reorder point for a given order quantity is the one at which the inventory costs at the start and at the end of a replenishment cycle are equal. This first-order condition is the basis for all the comparisons in the paper.
--
--   **Formalization Note** The paper writes "$r = r(Q)$" for "$r$ is an optimal reorder point for $Q$". Part 1 makes explicit the existence of an optimal reorder point, which the paper takes for granted when it writes "let $r(Q)$ be an optimal $r$ for $Q$ fixed" (p. 90). The standing assumption that $G$ has a unique minimizer (p. 90) is a hypothesis.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 90, Lemma 2

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Lemma 2 (Zheng 1992, p. 90): for any `Q > 0`, an optimal reorder point `r(Q)` exists (the
chosen one, `optReorder`, minimizes `c(Q, ·)`), and `r` minimizes `c(Q, ·)` iff
`G(r) = G(r + Q)`. -/
theorem reorder_opt_iff
    {lam L K h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 < Q) :
    IsOptReorder (newsvendorCost h p μ) lam K Q (optReorder (newsvendorCost h p μ) Q) ∧
    ∀ r : ℝ, IsOptReorder (newsvendorCost h p μ) lam K Q r ↔
      newsvendorCost h p μ r = newsvendorCost h p μ (r + Q) := by sorry

end ZhengQR.OrderQty
