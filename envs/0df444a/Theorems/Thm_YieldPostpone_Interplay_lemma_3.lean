-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_lemma_3
-- name    : YieldPostpone.Interplay.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:33.403983+00:00
-- url     : https://prove2.me/theorems/2e94dac0-ec0e-44e2-8e5d-457736d149c9
-- title:
--   Lemma 3, p. 12 with App. B.3, PDF p. 36 — the DA equilibrium exists, is unique in outcome and has two pieces split at c^DA
-- statement:
--   **Lemma 3** (scenario DA: pay-by-delivery, ex ante pricing). Let $a,b>0$, $0<\alpha,\theta<1$, $\mu=\alpha(1-\theta)+\theta$ and
--   $$c^{DA}=\frac{a\alpha(\mu-\theta\sqrt\mu)}{b(\alpha+\theta)}.$$
--   For every cost $0<c<a\mu/b$ the DA game has a subgame-perfect equilibrium, and every equilibrium has the outcome $(\pi^{DA}_R,\pi^{DA}_S,CS^{DA})$ equal to
--
--   $$\begin{cases}
--   \Big(\dfrac{(bc-a\alpha)^2}{16b\alpha^2},\ \dfrac{(bc-a\alpha)^2}{8b\alpha^2},\ \dfrac{(bc-a\alpha)^2}{32b\alpha^2}\Big), & 0<c<c^{DA},\\[3mm]
--   \Big(\dfrac{(bc-a\mu)^2}{16b\mu},\ \dfrac{(bc-a\mu)^2}{8b\mu},\ \dfrac{(bc-a\mu)^2(\alpha(2-\alpha)(1-\theta)+\theta)}{32b\mu^2}\Big), & c^{DA}<c<\dfrac ab\mu.
--   \end{cases}$$
--
--   The supplier inflates its production on the first piece and not on the second; the retailer never inflates its order.
--
--   **Formalization Note** "Uniquely defined" is stated as existence plus the value of the outcome at every equilibrium, on the open pieces. The equilibrium predicate uses the production tie rule described in the Setting. The "Moreover" sentence of the lemma (who inflates) is not part of this statement.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 12, Lemma 3; App. B.3, PDF p. 36 (appendix p. 4), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem lemma_3 (P : Params) (hP : P.Valid) :
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .DA σ) ∧
      ∀ σ : Profile, IsSPE P c .DA σ →
        (c < cDA P →
          piR P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) ∧
          piS P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) ∧
          CS P c .DA σ = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
        (cDA P < c →
          piR P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P) ∧
          piS P c .DA σ = (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P) ∧
          CS P c .DA σ = (P.b * c - P.a * μ P) ^ 2 *
            (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * μ P ^ 2)) := by sorry

end YieldPostpone.Interplay
