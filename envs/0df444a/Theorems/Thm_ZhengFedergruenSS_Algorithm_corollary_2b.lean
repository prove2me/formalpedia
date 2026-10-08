-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_corollary_2b
-- name    : ZhengFedergruenSS.Algorithm.corollary_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:38.266751+00:00
-- url     : https://prove2.me/theorems/9873b47c-b021-4638-b6b3-b8e38695ebc7
-- title:
--   Corollary 2(b), p. 657 — every s⁰ < y₁* satisfying (7) for some S is at most s_u*
-- statement:
--   In the model of Zheng and Federgruen, let $y_1^*$ be the smallest minimizer of $G$. Let $(s_u^*,S^*)$ be an optimal policy with $s_u^*<y_1^*$, and suppose $s_u^*$ is the largest $s<y_1^*$ for which $(s,S^*)$ is optimal. If $s^0<y_1^*$ is a reorder level for some order-up-to level $S$ (so $s^0<S$) satisfying (7),
--   $$G(s^0)\ge c(s^0,S)\ge G(s^0+1),$$
--   then $s^0\le s_u^*$.
--
--   This is a lower bound on optimal reorder levels. Every reorder level the algorithm produces is such a bound, which is why the inner loop of Step 1 only increases $s$.
--
--   **Formalization Note.** The page leaves $s^0<y_1^*$ implicit: the $s^0$ of (7) is that of Lemma 1(a). Without it the claim fails on the right tail of $G$.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 657, Corollary 2(b)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Corollary 2(b), p. 657 (Zheng and Federgruen 1991). Let `s_u*` denote the largest optimal reorder
level `< y₁*`; if `s⁰` satisfies (7) for some arbitrary order-up-to level `S`, then `s⁰ ≦ s_u*`.

Formalization Note: `s_u*` is the reorder level of an optimal policy `(s_u*, S*)` and is the largest
`s < y₁*` such that `(s, S*)` is optimal (the page's proof applies Lemma 1(c) at `S*`). The
hypothesis `s⁰ < y₁*` is implicit on the page (the `s⁰` of (7) is that of Lemma 1(a)); without it
the claim fails on the right tail of `G`. `s⁰ < S` because `s⁰` is a reorder level for `S`. -/
theorem corollary_2b (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₁ : ℤ) (hy₁ : IsLeast {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₁)
    (su Sstar : ℤ) (hsu : IsOptimalPolicy D.φ K G su Sstar) (hsuy : su < y₁)
    (hsu_max : ∀ s : ℤ, s < y₁ → IsOptimalPolicy D.φ K G s Sstar → s ≤ su)
    (S s₀ : ℤ) (hs₀y : s₀ < y₁) (hs₀S : s₀ < S)
    (h7 : G (s₀ + 1) ≤ c D.φ K G s₀ S ∧ c D.φ K G s₀ S ≤ G s₀) :
    s₀ ≤ su := by sorry

end ZhengFedergruenSS.Algorithm
