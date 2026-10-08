-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_lemma_2c
-- name    : ZhengFedergruenSS.Algorithm.lemma_2c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:36.32599+00:00
-- url     : https://prove2.me/theorems/e792edb0-d394-4d57-9159-c48211b7ccb7
-- title:
--   Lemma 2(c), p. 658 — any c ≧ c* gives the bound S̄_c, and S̄* ≦ S̄_{c₁} ≦ S̄_{c₂} for c* ≦ c₁ ≦ c₂
-- statement:
--   In the model of Zheng and Federgruen, let $y_2^*$ be the largest minimizer of $G$ and $c^*=c(s^*,S^*)$ the cost of an optimal policy $(s^*,S^*)$. For a number $c$ let
--   $$\bar S_c=\max\{y\ge y_2^*:\ G(y)\le c\},$$
--   whenever the maximum exists.
--
--   1. If $c\ge c^*$, then $S\le\bar S_c$ for every optimal policy $(s,S)$.
--   2. If $c^*\le c_1\le c_2$, then $\bar S^*\le\bar S_{c_1}\le\bar S_{c_2}$, where $\bar S^*=\bar S_{c^*}$.
--
--   The cost of any policy is an upper bound $c$ on $c^*$, so the bound tightens as better policies are found. The algorithm applies it with $c=c^0$.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 658, Lemma 2(c)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Lemma 2(c), p. 658 (Zheng and Federgruen 1991). Any upper bound `c` of `c*` defines an upper bound
`S̄_c = max{y ≧ y₂*: G(y) ≦ c}` of the order-up-to level of every optimal policy. Moreover
`S̄* ≦ S̄_{c₁} ≦ S̄_{c₂}` if `c* ≦ c₁ ≦ c₂`.

Formalization Note: `c* = c(s*, S*)` for a given optimal policy `(s*, S*)`; `S̄*`, `S̄_c`, `S̄_{c₁}`,
`S̄_{c₂}` are binders characterised as greatest elements of their sets. -/
theorem lemma_2c (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₂ : ℤ) (hy₂ : IsGreatest {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₂)
    (sstar Sstar : ℤ) (hopt : IsOptimalPolicy D.φ K G sstar Sstar) :
    (∀ (cbd : ℝ) (Sc : ℤ), c D.φ K G sstar Sstar ≤ cbd →
        IsGreatest {y : ℤ | y₂ ≤ y ∧ G y ≤ cbd} Sc →
        ∀ s S : ℤ, IsOptimalPolicy D.φ K G s S → S ≤ Sc) ∧
    (∀ (c₁ c₂ : ℝ) (Sbar S₁ S₂ : ℤ), c D.φ K G sstar Sstar ≤ c₁ → c₁ ≤ c₂ →
        IsGreatest {y : ℤ | y₂ ≤ y ∧ G y ≤ c D.φ K G sstar Sstar} Sbar →
        IsGreatest {y : ℤ | y₂ ≤ y ∧ G y ≤ c₁} S₁ →
        IsGreatest {y : ℤ | y₂ ≤ y ∧ G y ≤ c₂} S₂ →
        Sbar ≤ S₁ ∧ S₁ ≤ S₂) := by sorry

end ZhengFedergruenSS.Algorithm
