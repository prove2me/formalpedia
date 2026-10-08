-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_lemma_3b
-- name    : ZhengFedergruenSS.Algorithm.lemma_3b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:48.440042+00:00
-- url     : https://prove2.me/theorems/3f2730ae-7a21-46a4-a381-c0bf6a1592cd
-- title:
--   Lemma 3(b), p. 658 — after an improvement, s′ = min{y ≧ s⁰: c(y, S′) > G(y + 1)} is optimal for S′
-- statement:
--   In the model of Zheng and Federgruen, let $y_1^*$ be the smallest minimizer of $G$. Let $S^0\ge y_1^*$, let $s^0<y_1^*$ be an optimal reorder level for $S^0$, and assume (7) holds with $S=S^0$. If $c(s^0,S')<c(s^0,S^0)$ for some $S'\ge y_1^*$, then
--   $$s'=\min\{y\ge s^0:\ y<S',\ c(y,S')>G(y+1)\}$$
--   is an optimal reorder level for $S'$. Moreover $s'<y_1^*$ and
--   $$G(s')\ \ge\ c(s',S')\ >\ G(s'+1).$$
--
--   This justifies the inner loop of Step 1: after an improving $S'$ is found, the new optimal reorder level is reached by increasing the old one.
--
--   **Formalization Note.** $s'$ is a hypothesis-characterised integer, the least element of its set. The constraint $y<S'$ restricts to reorder levels for $S'$.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 658, Lemma 3(b)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Lemma 3(b), p. 658 (Zheng and Federgruen 1991). For a given order-up-to level `S⁰ (≧ y₁*)`, let
`s⁰ (< y₁*)` be an optimal reorder level, and assume that (7) holds with `S = S⁰`. If
`c(s⁰, S′) < c(s⁰, S⁰)` for some `S′ (≧ y₁*)`, then `s′ = min{y ≧ s⁰: c(y, S′) > G(y + 1)}` is
optimal for `S′`; moreover `s′ < y₁*` and `G(s′) ≧ c(s′, S′) > G(s′ + 1)`.

Formalization Note: `s′` is a binder (`IsLeast`); its set carries `y < S′`, the range of reorder
levels for `S′`. -/
theorem lemma_3b (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₁ : ℤ) (hy₁ : IsLeast {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₁)
    (S₀ s₀ : ℤ) (hS₀ : y₁ ≤ S₀) (hs₀y : s₀ < y₁) (hs₀opt : IsOptimalReorder D.φ K G S₀ s₀)
    (h7 : G (s₀ + 1) ≤ c D.φ K G s₀ S₀ ∧ c D.φ K G s₀ S₀ ≤ G s₀)
    (S' : ℤ) (hS' : y₁ ≤ S') (himp : c D.φ K G s₀ S' < c D.φ K G s₀ S₀)
    (s' : ℤ) (hs' : IsLeast {y : ℤ | s₀ ≤ y ∧ y < S' ∧ G (y + 1) < c D.φ K G y S'} s') :
    IsOptimalReorder D.φ K G S' s' ∧ s' < y₁ ∧
      G s' ≥ c D.φ K G s' S' ∧ c D.φ K G s' S' > G (s' + 1) := by sorry

end ZhengFedergruenSS.Algorithm
