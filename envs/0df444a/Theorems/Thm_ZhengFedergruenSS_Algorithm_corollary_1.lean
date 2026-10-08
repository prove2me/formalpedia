-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_corollary_1
-- name    : ZhengFedergruenSS.Algorithm.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:41.320821+00:00
-- url     : https://prove2.me/theorems/ba40a4f6-2656-4a13-8eef-9bbbd845cc7d
-- title:
--   Corollary 1, p. 657 — s⁰ = max{y < y₁*: c(y, S) ≦ G(y)} satisfies (7) and is optimal for S
-- statement:
--   In the model of Zheng and Federgruen, let $y_1^*$ be the smallest minimizer of $G$ and fix an order-up-to level $S$. Suppose the maximum
--   $$s^0=\max\{y<y_1^*:\ y<S,\ c(y,S)\le G(y)\}$$
--   exists. Then $G(s^0)\ge c(s^0,S)\ge G(s^0+1)$, which is (7), and $s^0$ is an optimal reorder level for $S$.
--
--   This is the stopping rule of Step 0 of the algorithm.
--
--   **Formalization Note.** The maximum is taken as a hypothesis (the page presupposes it exists). The constraint $y<S$ restricts to reorder levels for $S$, where $c(y,S)$ is defined.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 657, Corollary 1

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Corollary 1, p. 657 (Zheng and Federgruen 1991). For any order-up-to level `S`, let
`s⁰ = max{y < y₁*: c(y, S) ≦ G(y)}`. Then (7) holds, `G(s⁰) ≧ c(s⁰, S) ≧ G(s⁰ + 1)`, and `s⁰` is
an optimal reorder level for `S`.

Formalization Note: the maximum is a binder (`IsGreatest`), which states the page's
presupposition that it exists. Reorder levels for `S` are `< S`, so the set carries `y < S`. -/
theorem corollary_1 (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₁ : ℤ) (hy₁ : IsLeast {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₁)
    (S s₀ : ℤ) (hs₀ : IsGreatest {y : ℤ | y < y₁ ∧ y < S ∧ c D.φ K G y S ≤ G y} s₀) :
    (G (s₀ + 1) ≤ c D.φ K G s₀ S ∧ c D.φ K G s₀ S ≤ G s₀) ∧ IsOptimalReorder D.φ K G S s₀ := by sorry

end ZhengFedergruenSS.Algorithm
