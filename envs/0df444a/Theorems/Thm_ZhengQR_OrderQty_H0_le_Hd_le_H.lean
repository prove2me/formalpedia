-- Prove2me | Theorems.Thm_ZhengQR_OrderQty_H0_le_Hd_le_H
-- name    : ZhengQR.OrderQty.H0_le_Hd_le_H
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:52:46.917509+00:00
-- url     : https://prove2.me/theorems/25e96b3b-0da4-4210-bc89-e7efe1501499
-- title:
--   Lemma 7 — $H_0(Q) \le H_d(Q) \le H(Q)$ and $A(Q) \le A_d(Q)$
-- statement:
--   Under the standing assumptions of the model ($\lambda, L, h, p > 0$; the leadtime demand distribution $\mu$ is a probability measure, integrable, with mean $\lambda L$ and nonnegative support; $G$ has a unique minimizer $y^0$), let $H$, $H_0 = H - G(y^0)$ and $A$ be the curves of the stochastic model, and $H_d$, $A_d$ those of the EOQ model with the same $\lambda, L, h, p$. Then for every $Q \ge 0$,
--
--   $$H_0(Q) \le H_d(Q) \le H(Q), \qquad A(Q) \le A_d(Q).$$
--
--   For a given order quantity, the inventory costs of the stochastic model exceed those of the EOQ model, but the controllable part $H_0$ is smaller. This is the comparison behind all the bounds of §3.
--
--   **Formalization Note** The paper states no range for $Q$; the curves are defined on $[0, \infty)$ and the statement is made there.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 95, Lemma 7

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

/-- Lemma 7 (Zheng 1992, p. 95): for every `Q ≥ 0`, `H₀(Q) ≤ H_d(Q) ≤ H(Q)` and `A(Q) ≤ A_d(Q)`,
where `H`, `H₀`, `A` belong to the stochastic model and `H_d`, `A_d` to the EOQ model with the same
parameters. -/
theorem H0_le_Hd_le_H
    {lam L h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    H0fun (newsvendorCost h p μ) Q ≤ Hfun (eoqCost lam L h p) Q ∧
    Hfun (eoqCost lam L h p) Q ≤ Hfun (newsvendorCost h p μ) Q ∧
    Afun (newsvendorCost h p μ) Q ≤ Afun (eoqCost lam L h p) Q := by sorry

end ZhengQR.OrderQty
