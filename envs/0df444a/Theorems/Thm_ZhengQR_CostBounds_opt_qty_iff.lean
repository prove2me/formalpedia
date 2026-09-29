-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_opt_qty_iff
-- name    : ZhengQR.CostBounds.opt_qty_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:57:20.526873+00:00
-- url     : https://prove2.me/theorems/8ac18e40-5072-4bfe-ab77-a89d689d706c
-- title:
--   Eq. (8): Q > 0 is an optimal order quantity iff H(Q) = C(Q)
-- statement:
--   In the stochastic $(Q,r)$ model, with $H$ and $C$ as in §2, for every $Q>0$: $Q$ minimizes $C$ over $(0,\infty)$ if and only if
--   $$H(Q)=C(Q).$$
--
--   This is the first-order optimality condition for the order quantity, necessary and sufficient because $C$ is convex (Lemma 5).
--
--   **Formalization Note** "Optimal" means $Q>0$ and $C(Q)\le C(Q')$ for all $Q'>0$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 92, Eq. (8)

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

theorem opt_qty_iff (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    IsOptQty M.G M.lam M.K Q ↔ Hfun M.G M.lam M.K Q = Cfun M.G M.lam M.K Q := by sorry

end ZhengQR.CostBounds
