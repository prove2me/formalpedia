-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_dr_threshold_order
-- name    : YieldPostpone.Pricing.dr_threshold_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:46.577065+00:00
-- url     : https://prove2.me/theorems/bc00e7be-2c0b-4a8d-b563-78187effaae5
-- title:
--   App. C, proof of Proposition 5, PDF p. 39 — for α ≥ 9/16, c^DR_1 < c^DR_2 < c^DA
-- statement:
--   For $a, b > 0$, $\theta \in (0,1)$ and $9/16 \le \alpha < 1$, the cost thresholds of scenarios DR and DA are ordered:
--   $$c^{DR}_1 < c^{DR}_2 < c^{DA},$$
--   with $c^{DR}_1, c^{DR}_2$ from Appendix B.4 and $c^{DA}$ from Appendix B.3.
--
--   The ordering splits $(0, a\mu/b)$ into four intervals on which the DA and DR equilibria of Lemmas 3 and 4 are each given by a single piece; the comparison of Proposition 5(D) is made interval by interval.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. C, proof of Proposition 5, PDF p. 39 (appendix p. 7); also p. 13 and PDF p. 38

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem dr_threshold_order (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    cDR1 P < cDR2 P ∧ cDR2 P < cDA P := by sorry

end YieldPostpone.Pricing
