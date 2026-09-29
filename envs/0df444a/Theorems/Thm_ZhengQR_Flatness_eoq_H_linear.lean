-- Prove2me | Theorems.Thm_ZhengQR_Flatness_eoq_H_linear
-- name    : ZhengQR.Flatness.eoq_H_linear
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:07:05.598932+00:00
-- url     : https://prove2.me/theorems/4f5825ef-b4c4-47e2-b883-2fc61d133a85
-- title:
--   Eq. (18): in the EOQ model r_d(Q) = λL − hQ/(h + p) and H_d(Q) = hp/(h + p)·Q
-- statement:
--   Consider the EOQ model with backorders, i.e. the $(Q,r)$ machinery applied to the cost rate $G_d(y) = h(y-\lambda L)^+ + p(\lambda L - y)^+$. Let $r_d(Q)$ be an optimal reorder point for $Q$ and $H_d(Q) = G_d(r_d(Q))$ for $Q>0$, $H_d(0) = G_d(y^0_d)$. Then for every $Q \ge 0$,
--
--   $$H_d(Q) = \frac{hp}{h+p}\,Q,$$
--
--   and for $Q>0$ the optimal reorder point is
--   $$r_d(Q) = \lambda L - \frac{h}{h+p}\,Q.$$
--
--   Thus the EOQ counterpart of $H$ is the line of slope $hp/(h+p)$, the asymptotic slope of $H$ (Lemma 4).
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 94, Eq. (18) and the display of r_d(Q) above it

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem eoq_H_linear (M : QRModel) (Q : ℝ) (hQ : 0 ≤ Q) :
    (0 < Q → M.rd Q = M.lam * M.L - M.h / (M.h + M.p) * Q) ∧
      M.Hd Q = M.h * M.p / (M.h + M.p) * Q := by sorry

end ZhengQR.Flatness
