-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_lemma_1_i
-- name    : YieldPostpone.Interplay.lemma_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:38.08693+00:00
-- url     : https://prove2.me/theorems/5e5ba00c-8ead-40d5-923a-325470d098e2
-- title:
--   Lemma 1(i), p. 11 with App. B.1, PDF p. 34 — the signs of c^OA_1 and c^OA_2 on the regions H₁, H₂, H₃
-- statement:
--   **Lemma 1(i).** Let $a,b>0$, $0<\alpha,\theta<1$, and let $\theta_1(\alpha)$, $\theta_2(\alpha)$ and the regions
--   $$\mathcal H_1=\{0<\theta<\theta_1(\alpha)\},\quad \mathcal H_2=\{\theta_1(\alpha)<\theta<\theta_2(\alpha)\},\quad \mathcal H_3=\{\theta_2(\alpha)<\theta<1\}$$
--   be as in Appendix B.1. Then
--
--   1. if $(\alpha,\theta)\in\mathcal H_1$, then $0<c^{OA}_1<c^{OA}_2$;
--   2. if $(\alpha,\theta)\in\mathcal H_2$, then $c^{OA}_1\le0<c^{OA}_2$;
--   3. if $(\alpha,\theta)\in\mathcal H_3$, then $c^{OA}_2\le0$.
--
--   On $\mathcal H_3$, where full yield is likely, the first two pieces of the OA equilibrium of Lemma 1 are empty, and the retailer never inflates its order.
--
--   **Formalization Note** $\theta_2(\alpha)$ is the largest real root of the cubic of PDF p. 34 ("the third root"). The page writes the regions with $0\le\alpha\le1$; the model's range $0<\alpha<1$ is used.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 11, Lemma 1(i); App. B.1, PDF p. 34 (appendix p. 2)

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem lemma_1_i (P : Params) (hP : P.Valid) :
    (H1 P.α P.θ → 0 < cOA1 P ∧ cOA1 P < cOA2 P) ∧
    (H2 P.α P.θ → cOA1 P ≤ 0 ∧ 0 < cOA2 P) ∧
    (H3 P.α P.θ → cOA2 P ≤ 0) := by sorry

end YieldPostpone.Interplay
