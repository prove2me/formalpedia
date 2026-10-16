-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_lemma_3
-- name    : YieldPostpone.Pricing.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:28.963984+00:00
-- url     : https://prove2.me/theorems/4d1976f3-bb98-422f-be77-5c496287b2b9
-- title:
--   Lemma 3, p. 12 (App. B.3, PDF p. 36) — the DA equilibrium exists, is unique in outcome, and has two pieces in c
-- statement:
--   Scenario DA (pay-by-delivery, ex ante pricing). For admissible parameters and every cost $0 < c < a\mu/b$ a subgame-perfect equilibrium exists, and every equilibrium has the outcome $(\pi^{DA}_R, \pi^{DA}_S, CS^{DA})$ given by
--   $$\begin{cases}
--   \Big(\frac{(bc-a\alpha)^2}{16b\alpha^2},\ \frac{(bc-a\alpha)^2}{8b\alpha^2},\ \frac{(bc-a\alpha)^2}{32b\alpha^2}\Big) & 0 < c < c^{DA},\\[4pt]
--   \Big(\frac{(bc-a\mu)^2}{16b\mu},\ \frac{(bc-a\mu)^2}{8b\mu},\ \frac{(bc-a\mu)^2(\alpha(2-\alpha)(1-\theta)+\theta)}{32b\mu^2}\Big) & c^{DA} < c < \frac ab\mu,
--   \end{cases}$$
--   with $c^{DA} = a\alpha(\mu-\theta\sqrt\mu)/(b(\alpha+\theta))$.
--
--   This is the equilibrium under payment postponement with ex ante pricing, the baseline for pricing postponement under pay-by-delivery.
--
--   **Formalization Note.** The pieces are stated on open intervals of $c$ (at the threshold the outcome is not unique). "Continuous pieces" is not restated: each piece is an explicit continuous function of $c$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 12, Lemma 3; App. B.3, PDF p. 36 (appendix p. 4), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem lemma_3 (P : Params) (hP : P.Valid) :
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .DA σ) ∧
      ∀ σ : Profile, IsSPE P c .DA σ →
        (c < cDA P →
          outcome P c .DA σ =
            ((P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2),
             (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2),
             (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2))) ∧
        (cDA P < c →
          outcome P c .DA σ =
            ((P.b * c - P.a * μ P) ^ 2 / (16 * P.b * μ P),
             (P.b * c - P.a * μ P) ^ 2 / (8 * P.b * μ P),
             (P.b * c - P.a * μ P) ^ 2 * (P.α * (2 - P.α) * (1 - P.θ) + P.θ) /
               (32 * P.b * μ P ^ 2))) := by sorry

end YieldPostpone.Pricing
