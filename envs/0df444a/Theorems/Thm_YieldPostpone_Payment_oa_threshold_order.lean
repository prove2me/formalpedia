-- Prove2me | Theorems.Thm_YieldPostpone_Payment_oa_threshold_order
-- name    : YieldPostpone.Payment.oa_threshold_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:33.645035+00:00
-- url     : https://prove2.me/theorems/6b51d26e-7250-456f-98c1-e1e7ea8ecb5d
-- title:
--   Appendix C — OA thresholds precede DA threshold
-- statement:
--   For every valid yield distribution and demand curve, the two cost thresholds of scenario OA are strictly ordered below the DA threshold:
--
--   $$c^{OA}_1<c^{OA}_2<c^{DA}.$$
--
--   This order identifies the OA and DA formula pieces compared in Proposition 4(A). The thresholds depend on $(a,b,\alpha,\theta)$ but not on the production cost $c$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. C, proof of Proposition 4, PDF p. 38 (appendix p. 6)

import Definitions.Def_YieldPostpone_Payment_Setting

namespace YieldPostpone.Payment

theorem oa_threshold_order (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < cDA P := by sorry

end YieldPostpone.Payment
