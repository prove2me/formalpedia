-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_two_by_two_structure
-- name    : YoungConventions.RiskDominance.two_by_two_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:03:36.342434+00:00
-- url     : https://prove2.me/theorems/a733bc66-1859-4aa4-9325-4a5594e02891
-- title:
--   $2\times2$ games: acyclic, $L_\Gamma=1$, strict equilibria $(1,1),(2,2)$, recurrent classes $\{h_1\},\{h_2\}$
-- statement:
--   Let $\Gamma$ be a $2\times2$ game in normal form: $a_{11}>a_{21}$, $b_{11}>b_{12}$, $a_{22}>a_{12}$, $b_{22}>b_{21}$. Then
--   1. $\Gamma$ is acyclic;
--   2. $L_\Gamma=1$;
--   3. the strict pure-strategy Nash equilibria of $\Gamma$ are exactly $(1,1)$ and $(2,2)$;
--   4. for every $k\ge1$ and $m$ with $k\le m/3$ and every best-reply distribution $p$, the recurrent communication classes of adaptive play $P^0$ without mistakes are exactly
--   $$\{h_1\}\quad\text{and}\quad\{h_2\},\qquad h_1=((1,1),\dots,(1,1)),\ h_2=((2,2),\dots,(2,2)).$$
--
--   This sets up the computation of the stochastically stable convention: only the two resistances $r_{12}$ and $r_{21}$ matter.
--
--   **Formalization Note** Strategies $1,2$ are `0, 1 : Fin 2`. The page says that adaptive play has "two absorbing states" $h_1,h_2$; item 4 states the content of "Theorem 1 implies", namely that $P^0$ has no other recurrent class. $k\le m/3$ is written $3k\le m$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_unperturbed
import Definitions.Def_YoungConventions_RiskDominance_recurrentClasses
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash
import Definitions.Def_YoungConventions_RiskDominance_IsAcyclic
import Definitions.Def_YoungConventions_RiskDominance_bestReplyRadius
import Definitions.Def_YoungConventions_RiskDominance_convention
import Definitions.Def_YoungConventions_RiskDominance_Strat2
import Definitions.Def_YoungConventions_RiskDominance_payoff2x2
import Definitions.Def_YoungConventions_RiskDominance_IsNormalForm
import Definitions.Def_YoungConventions_RiskDominance_profile11
import Definitions.Def_YoungConventions_RiskDominance_profile22

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **The `2 × 2` case: acyclic, `L_Γ = 1`, and the two absorbing conventions.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 70
(PDF p. 15): "It is clear that `Γ` is acyclic and `L_Γ = 1`. Without loss of generality we may write
`Γ` in the form [table] where `a₁₁ > a₂₁`, `b₁₁ > b₁₂`, `a₂₂ > a₁₂`, and `b₂₂ > b₂₁`. The strict,
pure strategy Nash equilibria are `(1, 1)` and `(2, 2)`. Theorem 1 implies that, if `k ≤ m/3`,
adaptive play without mistakes has two absorbing states: `h₁ = ((1, 1), …, (1, 1))` and
`h₂ = ((2, 2), …, (2, 2))`."

Let `a, b` satisfy the four normal-form inequalities. Then
1. the game is acyclic;
2. `L_Γ = 1`;
3. the strict pure Nash equilibria are exactly `(1, 1)` and `(2, 2)`;
4. for `1 ≤ k` with `3k ≤ m` and every best-reply distribution `p`, the recurrent communication
   classes of `P⁰` are exactly `{h₁}` and `{h₂}`.

**Formalization Note.** Paper strategies `1, 2` are `0, 1 : Fin 2`. Reading of item 4: the two
absorbing states are always `h₁, h₂`; what "Theorem 1 implies" adds is that `P⁰` has no other
recurrent class (adaptive play converges to one of them), which is what the later resistance
computation uses. `k ≤ m/3` is `3 * k ≤ m` in `ℕ`. -/
theorem two_by_two_structure (a b : Fin 2 → Fin 2 → ℝ) (hab : IsNormalForm a b) :
    IsAcyclic (payoff2x2 a b) ∧
    bestReplyRadius (payoff2x2 a b) = 1 ∧
    (∀ s : (i : Fin 2) → Strat2 i, YoungConventions.AdaptivePlay.IsStrictNash (payoff2x2 a b) s ↔ s = profile11 ∨ s = profile22) ∧
    ∀ (k m : ℕ) [NeZero m], 1 ≤ k → 3 * k ≤ m →
      ∀ p : (i : Fin 2) → YoungConventions.AdaptivePlay.History Strat2 m → Strat2 i → ℝ,
        IsBestReplyDistribution (payoff2x2 a b) k p →
        recurrentClasses (unperturbed p) = {{convention profile11}, {convention profile22}} := by sorry

end YoungConventions.RiskDominance
