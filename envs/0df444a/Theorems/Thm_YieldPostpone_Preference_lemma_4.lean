-- Prove2me | Theorems.Thm_YieldPostpone_Preference_lemma_4
-- name    : YieldPostpone.Preference.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:29.4908+00:00
-- url     : https://prove2.me/theorems/f7e36f33-43ee-4105-93b9-e156c36e89e2
-- title:
--   Lemma 4, p. 13, with App. B.4, PDF p. 37 — for α ≥ 9/16 the DR equilibrium: existence and the outcome on each of three open pieces
-- statement:
--   Consider scenario DR (pay-by-delivery, responsive pricing) with parameters $a,b>0$, $\theta\in(0,1)$, $\mu=\alpha(1-\theta)+\theta$, and suppose $9/16\le\alpha<1$. Let
--   $$c^{DR}_1=\frac{a\alpha(1-\theta)\big(\mu^2+\theta-2\theta\sqrt{\alpha\mu(1-\alpha)(1-\theta)}\big)}{b\big(\alpha^2(1-\theta)^3+4\alpha\theta(1-\theta)+\theta(1+\theta)^2\big)},\qquad c^{DR}_2=\frac{a\alpha\mu(1-\theta)}{b(\mu+\theta)},$$
--   and write $m=\alpha^2(1-\theta)+\theta$. Then:
--
--   1. for every cost $0<c<a\mu/b$ a subgame-perfect equilibrium exists;
--   2. if $0<c<c^{DR}_1$, every equilibrium has
--   $$\big(\pi^{DR}_R,\pi^{DR}_S,CS^{DR}\big)=\Big(\tfrac{(bc-a\alpha)^2}{16b\alpha^2},\ \tfrac{(a\alpha-bc)^2}{8b\alpha^2},\ \tfrac{(bc-a\alpha)^2}{32b\alpha^2}\Big);$$
--   3. if $c^{DR}_1<c<c^{DR}_2$, every equilibrium has
--   $$\big(\pi^{DR}_R,\pi^{DR}_S,CS^{DR}\big)=\Big(\tfrac{\mu^2(a\alpha(1-\theta)-bc)^2}{4b\alpha^2(1-\theta)^2m},\ \tfrac{\mu\theta c(a\alpha(1-\theta)-bc)}{2\alpha^2(1-\theta)^2m},\ \tfrac{\mu^2(a\alpha(1-\theta)-bc)^2}{8b\alpha^2(1-\theta)^2m}\Big);$$
--   4. if $c^{DR}_2<c<a\mu/b$, every equilibrium has
--   $$\big(\pi^{DR}_R,\pi^{DR}_S,CS^{DR}\big)=\Big(\tfrac{(a\mu-bc)^2}{16bm},\ \tfrac{(a\mu-bc)^2}{8bm},\ \tfrac{(a\mu-bc)^2}{32bm}\Big).$$
--
--   This is the equilibrium of the scenario with both postponements. On the middle piece the supplier sets the wholesale price at the inflation threshold $c/(\alpha(1-\theta))$.
--
--   **Formalization Note** Equilibrium means the subgame-perfect equilibrium of the mission's setting, whose production clause resolves the supplier's indifference at $w=c/(\alpha(1-\theta))$ by $Q=q$; under the page's assignment of that tie to inflation, no equilibrium exists on the middle piece. The page's B.4 summary prints the middle-piece consumer surplus with $m^2$ in the denominator; that value is the surplus of full delivery of an order placed in anticipation of no inflation, which no single equilibrium produces. The equilibrium value, with $m$, is stated here; the retailer's and supplier's profits are as printed. The pieces are stated open (the page uses half-open pieces); at the thresholds the outcome is not unique. Parts (i) and (ii) of the lemma are not posed.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), p. 13, Lemma 4; App. B.4, PDF pp. 36–37 (appendix pp. 4–5), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- Lemma 4, p. 13, with the B.4 summary, PDF p. 37: scenario DR (pay-by-delivery,
responsive pricing) for `α ≥ 9/16`. For every cost `0 < c < aμ/b` a subgame-perfect
equilibrium exists, and every equilibrium has the outcome `(π_R, π_S, CS)` of B.4 on each
open piece `0 < c < c^DR_1`, `c^DR_1 < c < c^DR_2`, `c^DR_2 < c < aμ/b`. On the middle piece
`CS` is the equilibrium value `μ²(aα(1−θ) − bc)² / (8bα²(1−θ)²(α²(1−θ)+θ))` (the page prints
one more factor `α²(1−θ)+θ` in the denominator). -/
theorem lemma_4 (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b → ∃ σ : Profile, IsSPE P c .DR σ) ∧
    (∀ (c : ℝ) (σ : Profile), 0 < c → c < cDR1 P → IsSPE P c .DR σ →
      piR P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) ∧
      piS P c .DR σ = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) ∧
      CS P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
    (∀ (c : ℝ) (σ : Profile), cDR1 P < c → c < cDR2 P → IsSPE P c .DR σ →
      piR P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2
          / (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P c .DR σ = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c)
          / (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2
          / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ∧
    (∀ (c : ℝ) (σ : Profile), cDR2 P < c → c < P.a * μ P / P.b → IsSPE P c .DR σ →
      piR P c .DR σ = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by sorry

end YieldPostpone.Preference
