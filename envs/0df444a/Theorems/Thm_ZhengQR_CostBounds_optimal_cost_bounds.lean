-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_optimal_cost_bounds
-- name    : ZhengQR.CostBounds.optimal_cost_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:02:26.294985+00:00
-- url     : https://prove2.me/theorems/a673c51e-8e51-47ce-b634-48c15679b6d1
-- title:
--   Theorem 3: $C^*_0 \le \frac{Q^*_d}{Q^*}C^*_d$ and $C^*_d \le C^* \le G(y^0) + \frac{Q^*_d}{Q^*}C^*_d$
-- statement:
--   Consider the stochastic continuous-review $(Q,r)$ inventory model with demand rate $\lambda$, leadtime $L$, fixed ordering cost $K$, holding and backorder cost rates $h,p$ (all positive), and leadtime demand $D\ge0$ with $E(D)=\lambda L$, whose newsvendor cost $G(y)=E[h(y-D)^+ + p(D-y)^+]$ has a unique minimizer $y^0$. Let $Q^*$ be the optimal order quantity of the stochastic model, and write
--
--   - $C^*=C(Q^*)$ for its optimal average cost,
--   - $C^*_0=C_0(Q^*)$ for its optimal average controllable cost, where $C(Q)=G(y^0)+C_0(Q)$,
--   - $Q^*_d=\sqrt{2\lambda K(h+p)/(hp)}$ and $C^*_d=C_d(Q^*_d)$ for the optimal order quantity and optimal average cost of the EOQ model with the same parameters and demand constant at $\lambda L$.
--
--   Then
--   $$C^*_0\le\frac{Q^*_d}{Q^*}\,C^*_d,\qquad C^*_d\le C^*\le G(y^0)+\frac{Q^*_d}{Q^*}\,C^*_d.$$
--
--   The stochastic model's total optimal cost exceeds the EOQ's, while its controllable part is smaller, and the total gap is at most the newsboy cost $G(y^0)$ (as $Q^*_d\le Q^*$).
--
--   **Formalization Note** $C^*_d$ is taken as $C_d(Q^*_d)$; the milestone for Eqs. (18), (20) proves $Q^*_d$ is the unique minimizer of $C_d$, so this is the optimal EOQ cost. $C^*_0$ is taken as $C_0(Q^*)$; by Eq. (13), $C_0=C-G(y^0)$ on $(0,\infty)$, so $Q^*$ also minimizes $C_0$ and $C_0(Q^*)=\min_{Q>0}C_0(Q)$. The goal holds for every optimal $Q^*$; Lemma 6 shows exactly one exists.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 97, Theorem 3

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem optimal_cost_bounds (M : QRModel) (Qs : ℝ) (hQs : IsOptQty M.G M.lam M.K Qs) :
    C0fun M.G M.lam M.K Qs ≤ M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd ∧
    Cfun M.Gd M.lam M.K M.Qd ≤ Cfun M.G M.lam M.K Qs ∧
    Cfun M.G M.lam M.K Qs ≤ M.G (idealPt M.G) + M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd := by sorry

end ZhengQR.CostBounds
