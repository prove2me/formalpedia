-- Prove2me | Theorems.Thm_YieldPostpone_Preference_lemma_2
-- name    : YieldPostpone.Preference.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:21.217933+00:00
-- url     : https://prove2.me/theorems/631edc46-6335-4af5-8dcc-e745f4d7c417
-- title:
--   Lemma 2, p. 11, with App. B.2, PDF p. 35 — the OR equilibrium: existence, c^OR < aµ/b, and the outcome on each open piece
-- statement:
--   Consider scenario OR (pay-by-order, responsive pricing) with parameters $a,b>0$, $\alpha,\theta\in(0,1)$ and $\mu=\alpha(1-\theta)+\theta$. Then:
--
--   1. $c^{OR}<a\mu/b$, where $c^{OR}=\frac ab\alpha(1-\theta)\big((1-\alpha)-\sqrt{\alpha^2+\theta/(1-\theta)}\big)$;
--   2. for every cost $0<c<a\mu/b$ a subgame-perfect equilibrium exists;
--   3. if $0<c<c^{OR}$, every equilibrium has
--   $$\big(\pi^{OR}_R,\pi^{OR}_S,CS^{OR}\big)=\Big(\tfrac{(a\alpha(1-\theta)-bc)^2}{16b\alpha^2(1-\theta)}+\tfrac{a^2\theta}{4b},\ \tfrac{(a\alpha(1-\theta)-bc)^2}{8b\alpha^2(1-\theta)},\ \tfrac{(a\alpha(1-\theta)-bc)^2}{32b\alpha^2(1-\theta)}+\tfrac{a^2\theta}{8b}\Big);$$
--   4. if $\max\{0,c^{OR}\}<c<a\mu/b$, every equilibrium has
--   $$\big(\pi^{OR}_R,\pi^{OR}_S,CS^{OR}\big)=\Big(\tfrac{(a\mu-bc)^2}{16b(\alpha^2(1-\theta)+\theta)},\ \tfrac{(a\mu-bc)^2}{8b(\alpha^2(1-\theta)+\theta)},\ \tfrac{(a\mu-bc)^2}{32b(\alpha^2(1-\theta)+\theta)}\Big).$$
--
--   The equilibrium outcome of OR is thus uniquely determined on each open piece. Proposition 2 uses the second piece, which is the only relevant one when $\alpha\ge 9/16$.
--
--   **Formalization Note** Equilibrium means the subgame-perfect equilibrium of the mission's setting. The page states the pieces on $0\le c<\max\{0,c^{OR}\}$ and $\max\{0,c^{OR}\}\le c<a\mu/b$; at the threshold the supplier is indifferent between two wholesale prices with different outcomes, so uniqueness is stated on the open pieces only. Parts (i) and (ii) of the lemma are not posed.
-- source:
--   Geng, Guo, Xiao, Yang, …, SSRN 3546872 (author version), pp. 11–12, Lemma 2; App. B.2, PDF p. 35 (appendix p. 3), Summary

import Mathlib
import Definitions.Def_YieldPostpone_Preference_Setting

namespace YieldPostpone.Preference

/-- Lemma 2, pp. 11–12, with the B.2 summary, PDF p. 35: scenario OR (pay-by-order,
responsive pricing). For every cost `0 < c < aμ/b` a subgame-perfect equilibrium exists;
`c^OR < aμ/b`; and every equilibrium has the outcome `(π_R, π_S, CS)` of B.2 on each open
piece `0 < c < c^OR` and `max{0, c^OR} < c < aμ/b`. -/
theorem lemma_2 (P : Params) (hP : P.Valid) :
    cOR P < P.a * μ P / P.b ∧
    (∀ c : ℝ, 0 < c → c < P.a * μ P / P.b → ∃ σ : Profile, IsSPE P c .OR σ) ∧
    (∀ (c : ℝ) (σ : Profile), 0 < c → c < cOR P → IsSPE P c .OR σ →
      piR P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (16 * P.b * P.α ^ 2 * (1 - P.θ))
          + P.a ^ 2 * P.θ / (4 * P.b) ∧
      piS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2 * (1 - P.θ)) ∧
      CS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 / (32 * P.b * P.α ^ 2 * (1 - P.θ))
          + P.a ^ 2 * P.θ / (8 * P.b)) ∧
    (∀ (c : ℝ) (σ : Profile), max 0 (cOR P) < c → c < P.a * μ P / P.b → IsSPE P c .OR σ →
      piR P c .OR σ = (P.a * μ P - P.b * c) ^ 2 / (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 / (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by sorry

end YieldPostpone.Preference
