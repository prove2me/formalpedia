-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_lemma_2a
-- name    : ZhengFedergruenSS.Algorithm.lemma_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:43.959552+00:00
-- url     : https://prove2.me/theorems/faed20da-e57d-42a1-b094-e5fe60d43e4b
-- title:
--   Lemma 2(a), p. 657 — there is an optimal policy (s*, S*) with S* ≧ y₂*
-- statement:
--   In the model of Zheng and Federgruen, let $y_2^*$ be the largest minimizer of $G$. There exists an optimal $(s,S)$ policy $(s^*,S^*)$ with
--   $$S^*\ \ge\ \underline S = y_2^*.$$
--
--   This is Veinott and Wagner's lower bound on the optimal order-up-to level, reproved in this model. In particular an optimal $(s,S)$ policy exists.
--
--   **Formalization Note.** Optimality is among all pairs of integers $s'<S'$. The existence of an optimal policy is part of the conclusion.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 657, Lemma 2(a)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Lemma 2(a), p. 657 (Zheng and Federgruen 1991; Veinott and Wagner's lower bound for `S*`):
there exists an optimal policy `(s*, S*)` with `S* ≧ S̲ = y₂*`, the largest minimizer of `G`.

Formalization Note: optimality is among all integer pairs `s′ < S′` (`IsOptimalPolicy`). The
existence of an optimal policy is part of the conclusion, not an assumption. -/
theorem lemma_2a (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (y₂ : ℤ) (hy₂ : IsGreatest {y : ℤ | ∀ x : ℤ, G y ≤ G x} y₂) :
    ∃ sstar Sstar : ℤ, IsOptimalPolicy D.φ K G sstar Sstar ∧ y₂ ≤ Sstar := by sorry

end ZhengFedergruenSS.Algorithm
