-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_lemma_4
-- name    : YieldPostpone.Pricing.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:47.296842+00:00
-- url     : https://prove2.me/theorems/58771ded-318b-4010-b369-392fa43e235b
-- title:
--   Lemma 4, p. 13 (App. B.4, PDF p. 37) — for α ≥ 9/16 the DR equilibrium exists, is unique in outcome, and has three pieces in c
-- statement:
--   Scenario DR (pay-by-delivery, responsive pricing). Suppose $\alpha \ge 9/16$, with $a, b > 0$ and $\alpha, \theta \in (0,1)$. For every cost $0 < c < a\mu/b$ a subgame-perfect equilibrium exists. Writing $E_2 = \alpha^2(1-\theta)+\theta$ and $y = a\alpha(1-\theta) - bc$, every equilibrium has the outcome $(\pi^{DR}_R, \pi^{DR}_S, CS^{DR})$ given by
--   $$\begin{cases}
--   \Big(\frac{(bc-a\alpha)^2}{16b\alpha^2},\ \frac{(a\alpha-bc)^2}{8b\alpha^2},\ \frac{(bc-a\alpha)^2}{32b\alpha^2}\Big) & 0 < c < c^{DR}_1,\\[4pt]
--   \Big(\frac{\mu^2y^2}{4b\alpha^2(1-\theta)^2E_2},\ \frac{\mu\theta c\,y}{2\alpha^2(1-\theta)^2E_2},\ \frac{\mu^2y^2}{8b\alpha^2(1-\theta)^2E_2}\Big) & c^{DR}_1 < c < c^{DR}_2,\\[4pt]
--   \Big(\frac{(a\mu-bc)^2}{16bE_2},\ \frac{(a\mu-bc)^2}{8bE_2},\ \frac{(a\mu-bc)^2}{32bE_2}\Big) & c^{DR}_2 < c < \frac ab\mu .
--   \end{cases}$$
--
--   This is the equilibrium when the retailer uses both postponement strategies.
--
--   **Formalization Note.** The pieces are stated on open intervals of $c$. On the middle piece the supplier is indifferent between producing the order and inflating; the mission's equilibrium notion resolves the tie by producing the order, which is the choice that yields the paper's printed profits (under inflation at the tie this scenario has no equilibrium on that interval). Appendix B.4 prints the middle-piece consumer surplus with $E_2^2$ in the denominator; that value combines the order placed in anticipation of no inflation with full delivery under inflation, which no single equilibrium produces. The surplus of the equilibrium, with $E_2$ to the first power, is stated. "Continuous pieces" is not restated.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 13, Lemma 4; App. B.4, PDF pp. 36–37 (appendix pp. 4–5), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem lemma_4 (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .DR σ) ∧
      ∀ σ : Profile, IsSPE P c .DR σ →
        (c < cDR1 P →
          outcome P c .DR σ =
            ((P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2),
             (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2),
             (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2))) ∧
        (cDR1 P < c → c < cDR2 P →
          outcome P c .DR σ =
            (μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
                (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)),
             μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
                (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)),
             μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
                (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)))) ∧
        (cDR2 P < c →
          outcome P c .DR σ =
            ((P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)),
             (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)),
             (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)))) := by sorry

end YieldPostpone.Pricing
