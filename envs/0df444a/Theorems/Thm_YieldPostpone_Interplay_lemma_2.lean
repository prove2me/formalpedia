-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_lemma_2
-- name    : YieldPostpone.Interplay.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:28.028709+00:00
-- url     : https://prove2.me/theorems/d74467af-ca1b-4644-8c02-90e0530d99f6
-- title:
--   Lemma 2, pp. 11–12 with App. B.2, PDF p. 35 — the OR equilibrium exists, is unique in outcome and has two pieces split at max{0, c^OR}
-- statement:
--   **Lemma 2** (scenario OR: pay-by-order, responsive pricing). Let $a,b>0$, $0<\alpha,\theta<1$, $\mu=\alpha(1-\theta)+\theta$ and
--   $$c^{OR}=\frac ab\alpha(1-\theta)\Big((1-\alpha)-\sqrt{\alpha^2+\tfrac{\theta}{1-\theta}}\Big).$$
--   Then $c^{OR}<a\mu/b$, and for every cost $0<c<a\mu/b$ the OR game has a subgame-perfect equilibrium. Every equilibrium has the outcome $(\pi^{OR}_R,\pi^{OR}_S,CS^{OR})$ equal to
--
--   $$\begin{cases}
--   \Big(\dfrac{(a\alpha(1-\theta)-bc)^2}{16b\alpha^2(1-\theta)}+\dfrac{a^2\theta}{4b},\ \dfrac{(a\alpha(1-\theta)-bc)^2}{8b\alpha^2(1-\theta)},\ \dfrac{(a\alpha(1-\theta)-bc)^2}{32b\alpha^2(1-\theta)}+\dfrac{a^2\theta}{8b}\Big), & 0<c<\max\{0,c^{OR}\},\\[3mm]
--   \Big(\dfrac{(a\mu-bc)^2}{16b(\alpha^2(1-\theta)+\theta)},\ \dfrac{(a\mu-bc)^2}{8b(\alpha^2(1-\theta)+\theta)},\ \dfrac{(a\mu-bc)^2}{32b(\alpha^2(1-\theta)+\theta)}\Big), & \max\{0,c^{OR}\}<c<\dfrac ab\mu.
--   \end{cases}$$
--
--   The retailer inflates its order only on the first piece; the supplier always produces the ordered amount.
--
--   **Formalization Note** "Uniquely defined" is stated as existence plus the value of the outcome at every equilibrium, on the open pieces (at $c=c^{OR}$ the outcome is not unique).
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 11–12, Lemma 2; App. B.2, PDF p. 35 (appendix p. 3), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem lemma_2 (P : Params) (hP : P.Valid) :
    cOR P < P.a * μ P / P.b ∧
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OR σ) ∧
      ∀ σ : Profile, IsSPE P c .OR σ →
        (c < max 0 (cOR P) →
          piR P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (16 * P.b * P.α ^ 2 * (1 - P.θ)) + P.a ^ 2 * P.θ / (4 * P.b) ∧
          piS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (8 * P.b * P.α ^ 2 * (1 - P.θ)) ∧
          CS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (32 * P.b * P.α ^ 2 * (1 - P.θ)) + P.a ^ 2 * P.θ / (8 * P.b)) ∧
        (max 0 (cOR P) < c →
          piR P c .OR σ = (P.a * μ P - P.b * c) ^ 2 /
              (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          piS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 /
              (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          CS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 /
              (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by sorry

end YieldPostpone.Interplay
