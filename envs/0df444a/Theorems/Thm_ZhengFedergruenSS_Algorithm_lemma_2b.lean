-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_lemma_2b
-- name    : ZhengFedergruenSS.Algorithm.lemma_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:40.122991+00:00
-- url     : https://prove2.me/theorems/5872042c-7b31-433b-bebd-a384946886c7
-- title:
--   Lemma 2(b), p. 658 — every optimal policy has S* ≦ S̄* = max{y ≧ y₂*: G(y) ≦ c*}
-- statement:
--   In the model of Zheng and Federgruen, let $y_2^*$ be the largest minimizer of $G$, let $(s^*,S^*)$ be an optimal policy with cost $c^*=c(s^*,S^*)$, and let
--   $$\bar S^*=\max\{y\ge y_2^*:\ G(y)\le c^*\}.$$
--   Then $S^*\le\bar S^*$.
--
--   This upper bound on the optimal order-up-to level is the reason Step 1 can stop as soon as $G(S)>c^0$.
--
--   **Formalization Note.** $\bar S^*$ is a hypothesis-characterised integer, the greatest element of its set.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 658, Lemma 2(b)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Lemma 2(b), p. 658 (Zheng and Federgruen 1991; new upper bound for `S*`): for every optimal policy
`(s*, S*)`, `S* ≦ S̄* = max{y ≧ y₂*: G(y) ≦ c*}`, where `c* = c(s*, S*)` is the optimal average cost.

Formalization Note: `c*` is the cost of the given optimal policy (never an infimum); `S̄*` is a
binder characterised as the greatest element of its set. -/
theorem lemma_2b (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₂ : ℤ) (hy₂ : IsGreatest {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₂)
    (sstar Sstar : ℤ) (hopt : IsOptimalPolicy D.φ K G sstar Sstar)
    (Sbar : ℤ) (hSbar : IsGreatest {y : ℤ | y₂ ≤ y ∧ G y ≤ c D.φ K G sstar Sstar} Sbar) :
    Sstar ≤ Sbar := by sorry

end ZhengFedergruenSS.Algorithm
