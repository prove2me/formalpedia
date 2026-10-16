-- Prove2me | Theorems.Thm_YieldPostpone_Pricing_lemma_2_i
-- name    : YieldPostpone.Pricing.lemma_2_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:24:30.116125+00:00
-- url     : https://prove2.me/theorems/6d4e2e07-79d1-4380-8aaa-38f9893b98db
-- title:
--   Lemma 2(i), p. 11 — c^OR ≥ 0 if and only if α ≤ 1/2 and θ ≤ (1 − 2α)/(2(1 − α))
-- statement:
--   For $a, b > 0$ and $\alpha, \theta \in (0,1)$, the threshold
--   $$c^{OR} = \frac ab\,\alpha(1-\theta)\Big((1-\alpha) - \sqrt{\alpha^2 + \tfrac{\theta}{1-\theta}}\Big)$$
--   satisfies
--   $$c^{OR} \ge 0 \iff 0 < \alpha \le \tfrac12 \ \text{ and } \ 0 < \theta \le \frac{1-2\alpha}{2(1-\alpha)} .$$
--
--   So scenario OR has a low-cost piece, in which the retailer inflates its order, only when yield loss is both severe and likely. This is what makes the (W, L, W) case of Proposition 5(O)(iii) possible.
-- source:
--   Geng, Guo, Xiao, Yang, Supply Risk Mitigation in a Decentralized Supply Chain: Pricing Postponement or Payment Postponement?, SSRN 3546872 (author version), p. 11, Lemma 2(i); App. B.2, PDF p. 35

import Mathlib
import Definitions.Def_YieldPostpone_Pricing_Setting

namespace YieldPostpone.Pricing

theorem lemma_2_i (P : Params) (hP : P.Valid) :
    0 ≤ cOR P ↔ P.α ≤ 1 / 2 ∧ P.θ ≤ (1 - 2 * P.α) / (2 * (1 - P.α)) := by sorry

end YieldPostpone.Pricing
