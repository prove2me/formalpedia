-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_lemma_4
-- name    : YieldPostpone.Interplay.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:43.953159+00:00
-- url     : https://prove2.me/theorems/17158b77-654d-4d8c-b746-3b9087aab1d5
-- title:
--   Lemma 4, p. 13 with App. B.4, PDF p. 37 — for α ≥ 9/16 the DR equilibrium exists, is unique in outcome and has three pieces split at c^DR_1, c^DR_2
-- statement:
--   **Lemma 4** (scenario DR: pay-by-delivery, responsive pricing). Let $a,b>0$, $9/16\le\alpha<1$, $0<\theta<1$, $\mu=\alpha(1-\theta)+\theta$, $\sigma_2=\alpha^2(1-\theta)+\theta$, and let $c^{DR}_1$, $c^{DR}_2$ be the thresholds of Appendix B.4. For every cost $0<c<a\mu/b$ the DR game has a subgame-perfect equilibrium, and every equilibrium has the outcome $(\pi^{DR}_R,\pi^{DR}_S,CS^{DR})$ equal to
--
--   $$\begin{cases}
--   \Big(\dfrac{(bc-a\alpha)^2}{16b\alpha^2},\ \dfrac{(a\alpha-bc)^2}{8b\alpha^2},\ \dfrac{(bc-a\alpha)^2}{32b\alpha^2}\Big), & 0<c<c^{DR}_1,\\[3mm]
--   \Big(\dfrac{\mu^2(a\alpha(1-\theta)-bc)^2}{4b\alpha^2(1-\theta)^2\sigma_2},\ \dfrac{\mu\theta c(a\alpha(1-\theta)-bc)}{2\alpha^2(1-\theta)^2\sigma_2},\ \dfrac{\mu^2(a\alpha(1-\theta)-bc)^2}{8b\alpha^2(1-\theta)^2\sigma_2}\Big), & c^{DR}_1<c<c^{DR}_2,\\[3mm]
--   \Big(\dfrac{(a\mu-bc)^2}{16b\sigma_2},\ \dfrac{(a\mu-bc)^2}{8b\sigma_2},\ \dfrac{(a\mu-bc)^2}{32b\sigma_2}\Big), & c^{DR}_2<c<\dfrac ab\mu.
--   \end{cases}$$
--
--   On the middle piece the supplier posts exactly the price $c/(\alpha(1-\theta))$ at which it is indifferent to inflating production.
--
--   **Formalization Note** (1) The equilibrium predicate resolves the supplier's production tie toward $Q=q$ (see the Setting). With the page's tie rule (inflate at the tie) the DR game has no equilibrium on the middle piece; with $Q=q$ the middle piece's profits are exactly the printed ones. (2) The consumer surplus of the middle piece is printed with $\sigma_2^2$ in the denominator; that value combines the order placed in anticipation of no inflation with full delivery, which no equilibrium produces. The value of the equilibrium, $\mu^2(a\alpha(1-\theta)-bc)^2/(8b\alpha^2(1-\theta)^2\sigma_2)$, is stated (a brute-force solution gives $0.02176$ against $0.02165$ at $\alpha=0.8,\theta=0.5,c=0.2325$, $a=b=1$; the printed value is $0.02641$). (3) Statements are on the open pieces; at the thresholds the outcome is not unique.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 13, Lemma 4; App. B.4, PDF pp. 36–37 (appendix pp. 4–5), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem lemma_4 (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .DR σ) ∧
      ∀ σ : Profile, IsSPE P c .DR σ →
        (c < cDR1 P →
          piR P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) ∧
          piS P c .DR σ = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) ∧
          CS P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
        (cDR1 P < c → c < cDR2 P →
          piR P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          piS P c .DR σ = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
              (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          CS P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ∧
        (cDR2 P < c →
          piR P c .DR σ = (P.a * μ P - P.b * c) ^ 2 /
              (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          piS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 /
              (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          CS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 /
              (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by sorry

end YieldPostpone.Interplay
