-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_lemma_2
-- name    : YieldPostpone.Pricing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:29.775981+00:00
-- url     : https://prove2.me/theorems/b027e68f-767e-45ba-94a4-3c0e83f43914
-- title:
--   Lemma 2, p. 11 (App. B.2, PDF p. 35) — the OR equilibrium exists, is unique in outcome, and has two pieces in c
-- statement:
--   Scenario OR (pay-by-order, responsive pricing). For admissible parameters, $c^{OR} < a\mu/b$, and for every cost $0 < c < a\mu/b$ a subgame-perfect equilibrium exists. Writing $E_2 = \alpha^2(1-\theta)+\theta$, every equilibrium has the outcome $(\pi^{OR}_R, \pi^{OR}_S, CS^{OR})$ given by
--   $$\begin{cases}
--   \Big(\frac{(a\alpha(1-\theta)-bc)^2}{16b\alpha^2(1-\theta)} + \frac{a^2\theta}{4b},\ \frac{(a\alpha(1-\theta)-bc)^2}{8b\alpha^2(1-\theta)},\ \frac{(a\alpha(1-\theta)-bc)^2}{32b\alpha^2(1-\theta)} + \frac{a^2\theta}{8b}\Big) & 0 < c < \max\{0,c^{OR}\},\\[4pt]
--   \Big(\frac{(a\mu-bc)^2}{16bE_2},\ \frac{(a\mu-bc)^2}{8bE_2},\ \frac{(a\mu-bc)^2}{32bE_2}\Big) & \max\{0,c^{OR}\} < c < \frac ab\mu .
--   \end{cases}$$
--
--   This is the equilibrium after pricing postponement under a pay-by-order contract.
--
--   **Formalization Note.** The pieces are stated on open intervals of $c$ (at the threshold the outcome is not unique). "Continuous pieces" is not restated: each piece is an explicit continuous function of $c$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 11, Lemma 2; App. B.2, PDF p. 35 (appendix p. 3), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem lemma_2 (P : Params) (hP : P.Valid) :
    cOR P < P.a * μ P / P.b ∧
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OR σ) ∧
      ∀ σ : Profile, IsSPE P c .OR σ →
        (c < max 0 (cOR P) →
          outcome P c .OR σ =
            ((P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2 * (1 - P.θ))
                + P.a ^ 2 * P.θ / (4 * P.b),
             (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2 * (1 - P.θ)),
             (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2 * (1 - P.θ))
                + P.a ^ 2 * P.θ / (8 * P.b))) ∧
        (max 0 (cOR P) < c →
          outcome P c .OR σ =
            ((P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)),
             (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)),
             (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)))) := by sorry

end YieldPostpone.Pricing
