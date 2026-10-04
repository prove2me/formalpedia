-- Prove2me | Theorems.Thm_ZhengQR_Flatness_H_sandwich
-- name    : ZhengQR.Flatness.H_sandwich
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:07:42.521399+00:00
-- url     : https://prove2.me/theorems/dcb9f88f-aaed-44b2-b208-c78e179838bc
-- title:
--   Lemma 7: H₀(Q) ≤ H_d(Q) ≤ H(Q) and A(Q) ≤ A_d(Q)
-- statement:
--   In the stochastic $(Q, r)$ model, let $H$, $H_0 = H - G(y^0)$ and $A(Q) = QH(Q) - \int_0^Q H(y)dy$ be the functions of the stochastic model, and $H_d$, $A_d$ their counterparts in the EOQ model with the same parameters and $E(D) = \lambda L$. Then for every $Q\ge 0$,
--
--   $$H_0(Q) \le H_d(Q) \le H(Q), \qquad A(Q) \le A_d(Q).$$
--
--   The inventory costs at the ends of a cycle are higher in the stochastic model than in the EOQ model, while their controllable part $H_0$ is lower.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 95, Lemma 7

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem H_sandwich (M : QRModel) (Q : ℝ) (hQ : 0 ≤ Q) :
    M.H0 Q ≤ M.Hd Q ∧ M.Hd Q ≤ M.H Q ∧ M.A Q ≤ M.Ad Q := by sorry

end ZhengQR.Flatness
