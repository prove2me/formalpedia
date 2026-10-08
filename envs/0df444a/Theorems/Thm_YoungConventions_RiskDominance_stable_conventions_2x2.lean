-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_stable_conventions_2x2
-- name    : YoungConventions.RiskDominance.stable_conventions_2x2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:02:34.904537+00:00
-- url     : https://prove2.me/theorems/a6e63926-2510-452f-a3e0-8e2928b5eb0b
-- title:
--   Which convention is stochastically stable in a $2\times2$ game
-- statement:
--   Let $\Gamma$ be a $2\times2$ game in normal form, with $R_1,R_2$ as above and $h_1,h_2$ the two conventions.
--   1. If $R_1>R_2$, there is $K$ such that for all $k\ge\max(K,1)$, all $m\ge3k$, every best-reply distribution $p$ and every admissible experimentation $(\lambda,q)$, the unique stochastically stable state is $h_1$: a state $h$ is stochastically stable iff $h=h_1$.
--   2. If $R_1=R_2$, there is $K$ such that for the same range of $k,m,p,\lambda,q$ both $h_1$ and $h_2$ are stochastically stable.
--
--   **Formalization Note** "For all sufficiently large values of $k$ and $m/k$" is read as: $k$ beyond a threshold and $m/k\ge3$, the regime of generic stability ($k\le m/(L_\Gamma+2)$ with $L_\Gamma=1$). Item 1 is stated for all states, conventions or not.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
import Definitions.Def_YoungConventions_RiskDominance_IsStochasticallyStable
import Definitions.Def_YoungConventions_RiskDominance_convention
import Definitions.Def_YoungConventions_RiskDominance_Strat2
import Definitions.Def_YoungConventions_RiskDominance_payoff2x2
import Definitions.Def_YoungConventions_RiskDominance_IsNormalForm
import Definitions.Def_YoungConventions_RiskDominance_R1
import Definitions.Def_YoungConventions_RiskDominance_R2
import Definitions.Def_YoungConventions_RiskDominance_profile11
import Definitions.Def_YoungConventions_RiskDominance_profile22

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **Which convention is stochastically stable in a `2 × 2` game.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72 (PDF p. 17):
"If `R₁ > R₂`, then the unique stochastically stable convention is `h₁` for all sufficiently large
values of `k` and `m/k`. If `R₁ = R₂`, then both `h₁` and `h₂` are stochastically stable conventions
for all sufficiently large values of `k` and `m/k`."

For a `2 × 2` game in normal form:
1. if `R₁ > R₂`, there is `K` such that for all `k ≥ K` (`k ≥ 1`), all `m ≥ 3k`, every best-reply
   distribution `p` and every admissible `(λ, q)`, the stochastically stable states are exactly
   `h₁`;
2. if `R₁ = R₂`, there is `K` such that for the same range both `h₁` and `h₂` are stochastically
   stable.

**Formalization Note.** "For all sufficiently large values of `k` and `m/k`" is read as
`∃ K, ∀ k ≥ K, ∀ m ≥ 3k`, i.e. the threshold on `m/k` is `3` (the regime `k ≤ m/(L_Γ + 2)` of
generic stability); this is stronger than an unspecified threshold on `m/k`. Part 1 is stated for
all states `h`, not only conventions: "the unique stochastically stable convention is `h₁`" together
with the Corollary (no non-convention is stable). -/
theorem stable_conventions_2x2 (a b : Fin 2 → Fin 2 → ℝ) (hab : IsNormalForm a b) :
    (R2 a b < R1 a b → ∃ K : ℕ, ∀ k m : ℕ, K ≤ k → 1 ≤ k → 3 * k ≤ m → ∀ [NeZero m],
      ∀ (p q : (i : Fin 2) → YoungConventions.AdaptivePlay.History Strat2 m → Strat2 i → ℝ) (lam : Fin 2 → ℝ),
        IsBestReplyDistribution (payoff2x2 a b) k p → IsExperimentation lam q →
        ∀ h : YoungConventions.AdaptivePlay.History Strat2 m, IsStochasticallyStable p q lam h ↔ h = convention profile11) ∧
    (R1 a b = R2 a b → ∃ K : ℕ, ∀ k m : ℕ, K ≤ k → 1 ≤ k → 3 * k ≤ m → ∀ [NeZero m],
      ∀ (p q : (i : Fin 2) → YoungConventions.AdaptivePlay.History Strat2 m → Strat2 i → ℝ) (lam : Fin 2 → ℝ),
        IsBestReplyDistribution (payoff2x2 a b) k p → IsExperimentation lam q →
        IsStochasticallyStable p q lam (convention profile11) ∧
        IsStochasticallyStable p q lam (convention profile22)) := by sorry

end YoungConventions.RiskDominance
