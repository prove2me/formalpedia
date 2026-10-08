-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_lemma_3a
-- name    : ZhengFedergruenSS.Algorithm.lemma_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:38.537986+00:00
-- url     : https://prove2.me/theorems/fe800f83-897f-4fb4-96c7-779404719393
-- title:
--   Lemma 3(a), p. 658 (with (7) at S⁰) — c*(S) < c*(S⁰) iff c(s⁰, S) < c(s⁰, S⁰)
-- statement:
--   In the model of Zheng and Federgruen, let $y_1^*$ be the smallest minimizer of $G$. For an order-up-to level $S$ write $c^*(S)=\inf_{s<S}c(s,S)$. Let $S^0\ge y_1^*$, and let $s^0<y_1^*$ be an optimal reorder level for $S^0$ that satisfies (7) at $S^0$:
--   $$G(s^0)\ge c(s^0,S^0)\ge G(s^0+1).$$
--   Then for every $S>s^0$,
--   $$c^*(S)<c^*(S^0)\iff c(s^0,S)<c(s^0,S^0).$$
--
--   A single cost evaluation therefore decides whether $S$ improves on $S^0$; this is the test of the outer loop of Step 1.
--
--   **Formalization Note.** $c^*(S)<c^*(S^0)$ is stated as "some $s<S$ has $c(s,S)<c(s^0,S^0)$". This is equivalent, because $c^*(S^0)=c(s^0,S^0)$ and the minimum over $s<S$ need not be attained. Condition (7) at $S^0$ is an **added hypothesis**. The page assumes only that $s^0$ is optimal, and in that form the statement is false when the renewal density vanishes somewhere: for $p=(1/5,0,1/5,3/5)$, $m(1)=0$ and two adjacent reorder levels tie. Wherever the algorithm uses the lemma, (7) holds (Corollary 1, Lemma 3(b)).
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 658, Lemma 3(a)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Lemma 3(a), p. 658 (Zheng and Federgruen 1991). For a given order-up-to level `S⁰ (≧ y₁*)`, let
`s⁰ (< y₁*)` be an optimal reorder level. Then `c*(S) < c*(S⁰)` if and only if
`c(s⁰, S) < c(s⁰, S⁰)`, where `c*(S) = min_{s<S} c(s, S)`.

Formalization Note: `c*(S) < c*(S⁰)` is written `∃ s < S, c(s, S) < c(s⁰, S⁰)` (`c*(S⁰) = c(s⁰, S⁰)`
since `s⁰` is optimal for `S⁰`, and an infimum is below a number iff some value is); `c*(S)` is
never formed as an infimum, since the minimum over `s < S` need not be attained. `S > s⁰` so that
`c(s⁰, S)` is a policy cost. **Added hypothesis**: `s⁰` satisfies (7) at `S⁰`. Without it the
statement is false when the renewal density has a zero (e.g. `p = (1/5, 0, 1/5, 3/5)`, where
`m(1) = 0` makes two adjacent reorder levels tie); (7) at `S⁰` holds at every point where the
algorithm uses the lemma (Corollary 1, Lemma 3(b)). -/
theorem lemma_3a (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₁ : ℤ) (hy₁ : IsLeast {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₁)
    (S₀ s₀ : ℤ) (hS₀ : y₁ ≤ S₀) (hs₀y : s₀ < y₁) (hs₀opt : IsOptimalReorder D.φ K G S₀ s₀)
    (h7 : G (s₀ + 1) ≤ c D.φ K G s₀ S₀ ∧ c D.φ K G s₀ S₀ ≤ G s₀)
    (S : ℤ) (hS : s₀ < S) :
    (∃ s : ℤ, s < S ∧ c D.φ K G s S < c D.φ K G s₀ S₀) ↔ c D.φ K G s₀ S < c D.φ K G s₀ S₀ := by sorry

end ZhengFedergruenSS.Algorithm
