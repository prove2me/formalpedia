-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_threshold_order
-- name    : YieldPostpone.Interplay.threshold_order
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:33.056225+00:00
-- url     : https://prove2.me/theorems/51a0191c-bbb4-4783-92a2-33f01f33deac
-- title:
--   App. C, proofs of Propositions 1–3, PDF p. 38 — for α ≥ 9/16, c^OR < 0 and c^DR_1 < c^DR_2 < c^DA
-- statement:
--   Let $a,b>0$, $9/16\le\alpha<1$ and $0<\theta<1$. Then
--   $$c^{OR}<0\qquad\text{and}\qquad c^{DR}_1<c^{DR}_2<c^{DA}.$$
--
--   The first inequality says that for $\alpha\ge9/16$ only the second piece of the OR equilibrium (Lemma 2) is relevant. The second orders the cost thresholds of the two pay-by-delivery scenarios (Lemmas 3 and 4); together with Lemma 1(i) on $\mathcal H_3$, it splits the cost range $(0,a\mu/b)$ into the four intervals on which the interaction $V$ of Definition 1 is computed.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. C, PDF p. 38 (appendix p. 6), proof of Propositions 1 and 2 and proof of Proposition 3; also p. 13

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem threshold_order (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    cOR P < 0 ∧ cDR1 P < cDR2 P ∧ cDR2 P < cDA P := by sorry

end YieldPostpone.Interplay
