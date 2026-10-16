-- Prove2me | Theorems.Thm_YieldPostpone_Payment_responsive_threshold_order
-- name    : YieldPostpone.Payment.responsive_threshold_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:34.948277+00:00
-- url     : https://prove2.me/theorems/6490c9e7-4051-4836-9a2e-82b6dce48bcd
-- title:
--   Appendix C — responsive-pricing threshold order
-- statement:
--   When $\alpha\ge9/16$, the OR threshold is negative and the comparison threshold $\widetilde C$ lies strictly between zero and the first DR threshold. The two DR thresholds are also strictly ordered:
--
--   $$c^{OR}<0<\widetilde C<c^{DR}_1<c^{DR}_2.$$
--
--   The order identifies which equilibrium formula applies on each interval of Proposition 4(R). Here $\widetilde C$ is the explicit formula (6).
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. C, proofs of Propositions 1, 2 and 4, PDF p. 38 (appendix p. 6); (6), PDF p. 37 (appendix p. 5)

import Definitions.Def_YieldPostpone_Payment_Setting

namespace YieldPostpone.Payment

theorem responsive_threshold_order (P : Params) (hP : P.Valid)
    (hα : (9 : ℝ) / 16 ≤ P.α) :
    cOR P < 0 ∧ 0 < Ctil P ∧ Ctil P < cDR1 P ∧
      cDR1 P < cDR2 P := by sorry

end YieldPostpone.Payment
