-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_lemma_1
-- name    : YieldPostpone.Pricing.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:25.645566+00:00
-- url     : https://prove2.me/theorems/32d2c660-9b86-4377-b38e-cd046aa61023
-- title:
--   Lemma 1, p. 10 (App. B.1, PDF p. 35) — the OA equilibrium exists, is unique in outcome, and has three pieces in c
-- statement:
--   Scenario OA (pay-by-order, ex ante pricing). For admissible parameters $a, b > 0$, $\alpha, \theta \in (0,1)$, the thresholds satisfy
--   $$c^{OA}_1 < c^{OA}_2 < \frac ab\mu,$$
--   and for every cost $0 < c < a\mu/b$ a subgame-perfect equilibrium exists. Every equilibrium has the outcome $(\pi^{OA}_R, \pi^{OA}_S, CS^{OA})$ given by
--   $$\begin{cases}
--   \Big(\frac{(a\alpha-bc)^2}{16b\alpha^2},\ \frac{(a\alpha-bc)^2}{8b\alpha^2},\ \frac{(a\alpha-bc)^2}{32b\alpha^2}\Big) & 0 < c < \max\{0,c^{OA}_1\},\\[4pt]
--   \Big(\frac{(a\alpha-b\hat w)^2}{4b\alpha^2},\ \frac{(a\alpha-b\hat w)(\hat w-c)}{2\alpha^2},\ \frac{(a\alpha-b\hat w)^2}{8b\alpha^2}\Big) & \max\{0,c^{OA}_1\} < c < \max\{0,c^{OA}_2\},\\[4pt]
--   \Big(\frac{(a\mu-bc)^2}{16b\mu},\ \frac{(a\mu-bc)^2}{8b\mu},\ \frac{(a\mu-bc)^2(\alpha(2-\alpha)(1-\theta)+\theta)}{32b\mu^2}\Big) & \max\{0,c^{OA}_2\} < c < \frac ab\mu,
--   \end{cases}$$
--   where $\hat w = a\alpha(\mu-\theta\sqrt\mu)/(b(\alpha+\theta))$.
--
--   This is the equilibrium of the status-quo scenario against which both postponement strategies are measured.
--
--   **Formalization Note.** The lemma's pieces are stated on open intervals of $c$: at a threshold the supplier is indifferent between two wholesale prices with different outcomes, so the outcome is not unique there. The printed consumer surplus of the middle piece in Appendix B.1 has $8b\alpha^3$ in the denominator; the equilibrium of that piece (the retailer prices at $(a/b + \hat w/\alpha)/2$ and sells $(a\alpha-b\hat w)/(2\alpha)$ in both yield states) gives $8b\alpha^2$, confirmed by brute-force computation, and that is what is stated. "Continuous pieces" is not restated: each piece is an explicit continuous function of $c$.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 10, Lemma 1; App. B.1, PDF pp. 34–35 (appendix pp. 2–3), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem lemma_1 (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * μ P / P.b ∧
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      ∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) →
          outcome P c .OA σ =
            ((P.a * P.α - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2),
             (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2),
             (P.a * P.α - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2))) ∧
        (max 0 (cOA1 P) < c → c < max 0 (cOA2 P) →
          outcome P c .OA σ =
            ((P.a * P.α - P.b * what P) ^ 2 / (4 * P.b * P.α ^ 2),
             (P.a * P.α - P.b * what P) * (what P - c) / (2 * P.α ^ 2),
             (P.a * P.α - P.b * what P) ^ 2 / (8 * P.b * P.α ^ 2))) ∧
        (max 0 (cOA2 P) < c →
          outcome P c .OA σ =
            ((P.a * μ P - P.b * c) ^ 2 / (16 * P.b * μ P),
             (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P),
             (P.a * μ P - P.b * c) ^ 2 * (P.α * (2 - P.α) * (1 - P.θ) + P.θ) /
               (32 * P.b * μ P ^ 2))) := by sorry

end YieldPostpone.Pricing
