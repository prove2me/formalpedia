-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_lemma_1a
-- name    : ZhengFedergruenSS.Algorithm.lemma_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:26.404899+00:00
-- url     : https://prove2.me/theorems/6e285a25-4c2e-4fad-96f7-3a9257e0ba59
-- title:
--   Lemma 1(a), p. 656 — a reorder level s⁰ < y₁* satisfying (7) is optimal for S
-- statement:
--   In the model of Zheng and Federgruen, let $y_1^*$ be the smallest minimizer of $G$. Fix an order-up-to level $S$ and a reorder level $s^0<S$ with $s^0<y_1^*$. If
--   $$G(s^0)\ \ge\ c(s^0,S)\ \ge\ G(s^0+1), \tag{7}$$
--   then $s^0$ is an optimal reorder level for $S$: $c(s^0,S)=\min_{s<S}c(s,S)$. Moreover, $s^0-1$ is also optimal for $S$ if $G(s^0)=c(s^0,S)$, and $s^0+1$ is also optimal for $S$ if $G(s^0+1)=c(s^0,S)$.
--
--   Condition (7) is a local test that certifies global optimality in $s$ for fixed $S$. Both loops of the algorithm stop on it.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 656, Lemma 1(a), (7)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Lemma 1(a), p. 656 (Zheng and Federgruen 1991). For any order-up-to level `S`, a reorder level
`s⁰ < y₁*` (`y₁*` the smallest minimizer of `G`) is optimal for `S` if
`G(s⁰) ≧ c(s⁰, S) ≧ G(s⁰ + 1)` (7). Moreover `s⁰ − 1` (resp. `s⁰ + 1`) is also an optimal reorder
level for `S` if `G(s⁰) = c(s⁰, S)` (resp. `G(s⁰ + 1) = c(s⁰, S)`).

Formalization Note: a reorder level for `S` is an integer `s⁰ < S` (the cost `c(s, S)` is defined
for `s < S` only), so `s⁰ < S` is a hypothesis. `y₁*` is a binder characterised as the least
minimizer. -/
theorem lemma_1a (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₁ : ℤ) (hy₁ : IsLeast {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₁)
    (S s₀ : ℤ) (hs₀y : s₀ < y₁) (hs₀S : s₀ < S)
    (h7 : G (s₀ + 1) ≤ c D.φ K G s₀ S ∧ c D.φ K G s₀ S ≤ G s₀) :
    IsOptimalReorder D.φ K G S s₀ ∧
      (G s₀ = c D.φ K G s₀ S → IsOptimalReorder D.φ K G S (s₀ - 1)) ∧
      (G (s₀ + 1) = c D.φ K G s₀ S → IsOptimalReorder D.φ K G S (s₀ + 1)) := by sorry

end ZhengFedergruenSS.Algorithm
