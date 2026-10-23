-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_lemma_4_at_cDR2
-- name    : YieldPostpone.Interplay.lemma_4_at_cDR2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T02:40:13.245263+00:00
-- url     : https://prove2.me/theorems/252c01fb-7a69-4251-81dc-5734d5d7806c
-- title:
--   Lemma 4, p. 13 — at the threshold $c=c^{DR}_2$ the DR outcome takes its third-piece value
-- statement:
--   **Lemma 4 at the threshold $c=c^{DR}_2$** (scenario DR: pay-by-delivery, responsive pricing). Let $a,b>0$, $9/16\le\alpha<1$, $0<\theta<1$, $\mu=\alpha(1-\theta)+\theta$, $\sigma_2=\alpha^2(1-\theta)+\theta$ and
--   $$c^{DR}_2=\frac{a\alpha\mu(1-\theta)}{b(\mu+\theta)} .$$
--   At the cost $c=c^{DR}_2$, every subgame-perfect equilibrium of the DR game has the outcome
--   $$\big(\pi^{DR}_R,\ \pi^{DR}_S,\ CS^{DR}\big)=\Big(\frac{(a\mu-bc)^2}{16b\sigma_2},\ \frac{(a\mu-bc)^2}{8b\sigma_2},\ \frac{(a\mu-bc)^2}{32b\sigma_2}\Big),\qquad c=c^{DR}_2 .$$
--
--   Lemma 4 of the paper splits the cost range into the half-open pieces $c^{DR}_1\le c<c^{DR}_2$ and $c^{DR}_2\le c<\frac ab\mu$, so the threshold $c^{DR}_2$ itself belongs to the third piece; this statement is that endpoint case, which the mission's Lemma 4 milestone (stated on open pieces) leaves out. At $c^{DR}_2$ the middle and third formulas of Lemma 4 coincide: the supplier's boundary price $c/(\alpha(1-\theta))$ of the middle piece equals the interior optimum of the third piece.
--
--   The endpoint matters for Proposition 3: $c^{DR}_2$ lies inside the interval $(\hat C,c^{DA})$ on which the interaction $V$ is claimed negative.
--
--   **Formalization Note** The equilibrium predicate is the mission's `IsSPE` (production tie resolved toward $Q=q$), and the profits and surplus are its path values `piR`, `piS`, `CS`; the formulas are those of the third piece of the mission's `lemma_4`, evaluated at $c=c^{DR}_2$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 13, Lemma 4 (pieces $c^{DR}_1\le c<c^{DR}_2$ and $c^{DR}_2\le c<\frac ab\mu$); App. B.4, PDF p. 37

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem lemma_4_at_cDR2 (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    ∀ σ : Profile, IsSPE P (cDR2 P) .DR σ →
      piR P (cDR2 P) .DR σ = (P.a * μ P - P.b * cDR2 P) ^ 2 /
          (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P (cDR2 P) .DR σ = (P.a * μ P - P.b * cDR2 P) ^ 2 /
          (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P (cDR2 P) .DR σ = (P.a * μ P - P.b * cDR2 P) ^ 2 /
          (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by sorry

end YieldPostpone.Interplay
