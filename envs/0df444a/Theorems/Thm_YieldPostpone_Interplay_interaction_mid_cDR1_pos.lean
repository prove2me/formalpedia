-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_interaction_mid_cDR1_pos
-- name    : YieldPostpone.Interplay.interaction_mid_cDR1_pos
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T02:40:18.762527+00:00
-- url     : https://prove2.me/theorems/0d77d900-cfe8-411a-8ec0-ac88b17281a9
-- title:
--   App. C, proof of Proposition 3 — the middle-piece interaction is positive at $c=c^{DR}_1$
-- statement:
--   Let $a,b>0$, $9/16\le\alpha<1$, $0<\theta<1$, $\mu=\alpha(1-\theta)+\theta$, $\sigma_2=\alpha^2(1-\theta)+\theta$, and let $c^{DR}_1$ be the threshold of App. B.4,
--   $$c^{DR}_1=\frac{a\alpha(1-\theta)\big(\mu^2+\theta-2\theta\sqrt{\alpha\mu(1-\alpha)(1-\theta)}\big)}{b\big(\alpha^2(1-\theta)^3+4\alpha\theta(1-\theta)+\theta(1+\theta)^2\big)} .$$
--   For a cost $c$ define
--   $$V_{\rm mid}(c)=\frac{\mu^2(a\alpha(1-\theta)-bc)^2}{4b\alpha^2(1-\theta)^2\sigma_2}-\frac{(a\mu-bc)^2}{16b\sigma_2}-\Big(\frac{(bc-a\alpha)^2}{16b\alpha^2}-\frac{(a\mu-bc)^2}{16b\mu}\Big).$$
--   Then
--   $$V_{\rm mid}\big(c^{DR}_1\big)>0 .$$
--
--   On $\mathcal H_3$ with $\alpha\ge 9/16$, for $c^{DR}_1<c<c^{DR}_2$ the four retailer profits are: $\pi^{DR}_R$ from the middle piece of Lemma 4, $\pi^{OR}_R=(a\mu-bc)^2/(16b\sigma_2)$ (Lemma 2, since $c^{OR}<0$), $\pi^{DA}_R=(bc-a\alpha)^2/(16b\alpha^2)$ (Lemma 3, since $c<c^{DA}$) and $\pi^{OA}_R=(a\mu-bc)^2/(16b\mu)$ (Lemma 1, since $c^{OA}_2\le0$). So $V_{\rm mid}(c)$ is the interaction $V=(\pi^{DR}_R-\pi^{OR}_R)-(\pi^{DA}_R-\pi^{OA}_R)$ of Definition 1 on that interval, and the statement says that $V$ starts positive just above $c^{DR}_1$, where the retailer's DR profit jumps up as the supplier switches from inflating production to posting the price $c/(\alpha(1-\theta))$. Since $V_{\rm mid}$ is a convex quadratic in $c$ that is negative at $c^{DR}_2$, this gives the single sign change $\hat C$ of Proposition 3 on $(c^{DR}_1,c^{DR}_2)$: the postponements are complements on $(c^{DR}_1,\hat C)$ and substitutes on $(\hat C,c^{DR}_2)$.
--
--   **Formalization Note** The paper's closed form (7) for $\hat C$ is not used (see the note on Proposition 3); this statement isolates the sign fact that the existence of $\hat C$ rests on. The hypothesis $\alpha\ge9/16$ is the paper's standing assumption for Proposition 3 and Lemma 4; membership in $\mathcal H_3$ is not needed for this inequality.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), App. C, Proof of Proposition 3, PDF pp. 38–39 (sign of $V$ just above $c^{DR}_1$); thresholds from App. B.4, PDF p. 37; Lemma 4, p. 13

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem interaction_mid_cDR1_pos (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    0 < μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * cDR1 P) ^ 2 /
          (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))
        - (P.a * μ P - P.b * cDR1 P) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))
        - ((P.b * cDR1 P - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2)
          - (P.a * μ P - P.b * cDR1 P) ^ 2 / (16 * P.b * μ P)) := by sorry

end YieldPostpone.Interplay
