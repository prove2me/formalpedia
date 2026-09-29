-- Prove2me | Theorems.Thm_ZhengQR_Flatness_integral_H_le
-- name    : ZhengQR.Flatness.integral_H_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:08:40.990838+00:00
-- url     : https://prove2.me/theorems/19f700bf-643b-476b-8121-6fe8b572ee60
-- title:
--   Lemma 9: ∫_Q^{αQ} H(y)dy ≤ ((α² − 1)/2)·QH(Q) for all α > 0, Q > 0
-- statement:
--   In the stochastic $(Q, r)$ model, let $H(Q) = G(r(Q))$. For any $\alpha>0$ and $Q>0$,
--
--   $$\int_Q^{\alpha Q} H(y)\,dy \le \frac{\alpha^2-1}{2}\, Q\, H(Q).$$
--
--   For $\alpha<1$ the integral is oriented, $\int_Q^{\alpha Q} = -\int_{\alpha Q}^{Q}$, so the statement is then the lower bound $\int_{\alpha Q}^{Q} H(y)\,dy \ge \frac{1-\alpha^2}{2}\,QH(Q)$. The lemma bounds the change in the inventory-cost part of $C$ when the order quantity is scaled by $\alpha$, and is the key step of the flatness theorem.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 98, Lemma 9

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem integral_H_le (M : QRModel) (α Q : ℝ) (hα : 0 < α) (hQ : 0 < Q) :
    (∫ y in Q..α * Q, M.H y) ≤ (α ^ 2 - 1) / 2 * Q * M.H Q := by sorry

end ZhengQR.Flatness
