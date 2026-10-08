-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_theorem_1a
-- name    : ZhengFedergruenSS.Algorithm.theorem_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:58:33.127556+00:00
-- url     : https://prove2.me/theorems/dbe847c8-50b7-4006-8eb5-1029fb129063
-- title:
--   Theorem 1(a), p. 660 — the algorithm terminates with (s, S⁰) an optimal policy and c⁰ = c*
-- statement:
--   Let one-period demands be i.i.d. on $\{0,1,2,\dots\}$ with $p_0<1$, let $K>0$, and let $G:\mathbb Z\to\mathbb R$ be such that $-G$ is unimodal and $\lim_{|y|\to\infty}G(y)>\min_yG(y)+K$. Let $y^*$ be any minimum point of $G$. Then the algorithm of §3, started at $y^*$:
--
--   1. **terminates** after finitely many steps, and
--   2. on termination, with final values $s$, $S^0$, $c^0$, the pair $(s,S^0)$ is an **optimal policy** and $c^0=c(s,S^0)=c^*$:
--   $$c(s,S^0)\ \le\ c(s',S')\quad\text{for all integers } s'<S'.$$
--
--   This is the paper's main result. Together with Theorem 1(b) (not formalized here) it says that an optimal $(s,S)$ policy is found with about as much work as evaluating a single policy.
--
--   **Formalization Note.** Termination is part of the conclusion: some finite number of elementary steps reaches the terminated phase. Optimality is among all integer pairs $s'<S'$, not only those the algorithm visits. $c^*$ is the cost of an optimal policy, so "$c^0=c^*$" is $c^0=c(s,S^0)$ together with optimality. The growth condition is the page's, weaker than $G\to+\infty$. $y^*$ is any minimizer of $G$, not necessarily the smallest.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 660, Theorem 1(a)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model
import Definitions.Def_ZhengFedergruenSS_Algorithm_Run

namespace ZhengFedergruenSS.Algorithm

/-- Theorem 1(a), p. 660 (Zheng and Federgruen 1991): the algorithm of §3 (p. 659), started at any
minimum point `y*` of `G`, terminates with `(s, S⁰)` being an optimal policy and `c⁰ = c*`.

Formalization Note: termination is the first conjunct (some finite number of elementary steps
reaches the `done` phase; `run` returns `none` until then). Optimality is among **all** integer
pairs `s′ < S′` (`IsOptimalPolicy`), not only those the algorithm visits. `c* = c(s, S⁰)` for the
optimal `(s, S⁰)`, so "`c⁰ = c*`" is `c⁰ = c(s, S⁰)` together with optimality. `y*` is any
minimizer, not necessarily the smallest. The growth assumption is `GrowthCond`, weaker than
`G → +∞`. -/
theorem theorem_1a (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (ystar : ℤ) (hystar : ∀ x : ℤ, G ystar ≤ G x) :
    (∃ (n : ℕ) (out : ℤ × ℤ × ℝ), run D.φ K G ystar n = some out) ∧
      ∀ (n : ℕ) (s S₀ : ℤ) (c₀ : ℝ), run D.φ K G ystar n = some (s, S₀, c₀) →
        IsOptimalPolicy D.φ K G s S₀ ∧ c₀ = c D.φ K G s S₀ := by sorry

end ZhengFedergruenSS.Algorithm
