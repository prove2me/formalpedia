-- Prove2me | Theorems.Thm_YieldPostpone_Interplay_lemma_1
-- name    : YieldPostpone.Interplay.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:31.435991+00:00
-- url     : https://prove2.me/theorems/2b05bf5c-74c0-49e9-accd-29a4a019df6e
-- title:
--   Lemma 1, pp. 10–11 with App. B.1, PDF p. 35 — the OA equilibrium exists, is unique in outcome and has three pieces split at max{0, c^OA_1}, max{0, c^OA_2}
-- statement:
--   **Lemma 1** (scenario OA: pay-by-order, ex ante pricing). Let $a,b>0$, $0<\alpha,\theta<1$, $\mu=\alpha(1-\theta)+\theta$, and let $c^{OA}_1$, $c^{OA}_2$ and $\hat w=\dfrac{a\alpha(\mu-\theta\sqrt\mu)}{b(\alpha+\theta)}$ be the thresholds of Appendix B.1. Then $c^{OA}_1<c^{OA}_2<a\mu/b$, and for every cost $0<c<a\mu/b$ the OA game has a subgame-perfect equilibrium. Every equilibrium has the outcome $(\pi^{OA}_R,\pi^{OA}_S,CS^{OA})$ equal to
--
--   $$\begin{cases}
--   \Big(\dfrac{(a\alpha-bc)^2}{16b\alpha^2},\ \dfrac{(a\alpha-bc)^2}{8b\alpha^2},\ \dfrac{(a\alpha-bc)^2}{32b\alpha^2}\Big), & 0<c<\max\{0,c^{OA}_1\},\\[3mm]
--   \Big(\dfrac{(a\alpha-b\hat w)^2}{4b\alpha^2},\ \dfrac{(a\alpha-b\hat w)(\hat w-c)}{2\alpha^2},\ \dfrac{(a\alpha-b\hat w)^2}{8b\alpha^2}\Big), & \max\{0,c^{OA}_1\}<c<\max\{0,c^{OA}_2\},\\[3mm]
--   \Big(\dfrac{(a\mu-bc)^2}{16b\mu},\ \dfrac{(a\mu-bc)^2}{8b\mu},\ \dfrac{(a\mu-bc)^2(\alpha(2-\alpha)(1-\theta)+\theta)}{32b\mu^2}\Big), & \max\{0,c^{OA}_2\}<c<\dfrac ab\mu.
--   \end{cases}$$
--
--   In the first two pieces the retailer inflates its order to hedge the yield loss; in the third it does not.
--
--   **Formalization Note** (1) "Uniquely defined" is stated as existence of an equilibrium together with the value of the outcome at every equilibrium, on the open pieces: at a threshold the supplier is indifferent between two prices whose outcomes differ. (2) The consumer surplus of the middle piece is printed as $(a\alpha-b\hat w)^2/(8b\alpha^3)$ on PDF p. 35. With the inflated order every unit demanded at the price $p=(a/b+\hat w/\alpha)/2$ is delivered, so $CS=(a-bp)^2/(2b)=(a\alpha-b\hat w)^2/(8b\alpha^2)$, consistent with the first piece; a brute-force solution of the game agrees (e.g. $0.005363$ against $0.005353$ at $\alpha=0.5,\theta=0.1,c=0.3238$, $a=b=1$; the printed value is $0.010706$). The corrected value is stated. (3) The page's $[x]^+=\min\{0,x\}$ is read as $\max\{0,x\}$, as in the lemma itself. (4) $c^{OA}_2$ is the larger root of the quadratic given in the Setting.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), pp. 10–11, Lemma 1; App. B.1, PDF pp. 34–35 (appendix pp. 2–3), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting

namespace YieldPostpone.Interplay

theorem lemma_1 (P : Params) (hP : P.Valid) :
    cOA1 P < cOA2 P ∧ cOA2 P < P.a * μ P / P.b ∧
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OA σ) ∧
      ∀ σ : Profile, IsSPE P c .OA σ →
        (c < max 0 (cOA1 P) →
          piR P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2) ∧
          piS P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) ∧
          CS P c .OA σ = (P.a * P.α - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
        (max 0 (cOA1 P) < c → c < max 0 (cOA2 P) →
          piR P c .OA σ = (P.a * P.α - P.b * what P) ^ 2 / (4 * P.b * P.α ^ 2) ∧
          piS P c .OA σ = (P.a * P.α - P.b * what P) * (what P - c) / (2 * P.α ^ 2) ∧
          CS P c .OA σ = (P.a * P.α - P.b * what P) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
        (max 0 (cOA2 P) < c →
          piR P c .OA σ = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * μ P) ∧
          piS P c .OA σ = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * μ P) ∧
          CS P c .OA σ = (P.a * μ P - P.b * c) ^ 2 *
            (P.α * (2 - P.α) * (1 - P.θ) + P.θ) / (32 * P.b * μ P ^ 2)) := by sorry

end YieldPostpone.Interplay
