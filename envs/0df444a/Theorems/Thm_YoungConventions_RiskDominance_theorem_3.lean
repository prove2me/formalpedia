-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_theorem_3
-- name    : YoungConventions.RiskDominance.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:07:19.106493+00:00
-- url     : https://prove2.me/theorems/5985c291-d137-438f-9e1f-2ae4cb0c5369
-- title:
--   Theorem 3 — in $2\times2$ games the generically stable equilibria are the weakly risk dominant ones
-- statement:
--   Let $\Gamma$ be a $2\times2$ matrix game with two strict Nash equilibria in pure strategies, written in normal form
--   $$a_{11}>a_{21},\qquad b_{11}>b_{12},\qquad a_{22}>a_{12},\qquad b_{22}>b_{21},$$
--   so that the strict equilibria are $(1,1)$ and $(2,2)$, and let
--   $$R_1=\min\Big\{\tfrac{a_{11}-a_{21}}{a_{11}-a_{12}-a_{21}+a_{22}},\tfrac{b_{11}-b_{12}}{b_{11}-b_{12}-b_{21}+b_{22}}\Big\},\quad R_2=\min\Big\{\tfrac{a_{22}-a_{12}}{a_{11}-a_{12}-a_{21}+a_{22}},\tfrac{b_{22}-b_{21}}{b_{11}-b_{12}-b_{21}+b_{22}}\Big\}.$$
--   $(1,1)$ weakly risk dominates $(2,2)$ if $R_1\ge R_2$, and $(2,2)$ weakly risk dominates $(1,1)$ if $R_2\ge R_1$. Then the generically stable equilibria are the weakly risk dominant ones:
--   $$(1,1)\text{ is generically stable}\iff R_1\ge R_2,\qquad (2,2)\text{ is generically stable}\iff R_2\ge R_1.$$
--
--   Generic stability refers to the stationary distributions of adaptive play with mistakes, for all sufficiently large sample sizes $k$ with $k\le m/(L_\Gamma+2)$ and for every best-reply distribution and admissible experimentation. The theorem shows that the evolutionary selection of adaptive play agrees in $2\times2$ games with the risk-dominance criterion of Harsanyi and Selten.
--
--   **Formalization Note** The game is stated in the paper's normal form (any $2\times2$ game with two strict pure equilibria takes this form after relabelling). Strategies $1,2$ are `0, 1 : Fin 2`. "$(2,2)$ weakly risk dominates $(1,1)$ if $R_2\ge R_1$" is the symmetric reading the page leaves implicit. $L_\Gamma$ is computed from the game; it equals $1$ here.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72, Theorem 3

import Mathlib
import Definitions.Def_YoungConventions_RiskDominance_IsGenericallyStable
import Definitions.Def_YoungConventions_RiskDominance_Strat2
import Definitions.Def_YoungConventions_RiskDominance_payoff2x2
import Definitions.Def_YoungConventions_RiskDominance_IsNormalForm
import Definitions.Def_YoungConventions_RiskDominance_R1
import Definitions.Def_YoungConventions_RiskDominance_R2
import Definitions.Def_YoungConventions_RiskDominance_profile11
import Definitions.Def_YoungConventions_RiskDominance_profile22

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **Theorem 3.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72 (PDF p. 17): "Let `Γ` be a `2 × 2` matrix game with two strict
Nash equilibria in pure strategies. The generically stable equilibria are the weakly risk dominant
Nash equilibria."

Let `Γ` be a `2 × 2` game written in the normal form of p. 70: `a₁₁ > a₂₁`, `b₁₁ > b₁₂`,
`a₂₂ > a₁₂`, `b₂₂ > b₂₁`, so that its strict pure equilibria are `(1, 1)` and `(2, 2)`. With
`R₁, R₂` as on pp. 71–72, "`(1, 1)` weakly risk dominates `(2, 2)` if `R₁ ≥ R₂`" (p. 72). Then
`(1, 1)` is generically stable iff `R₁ ≥ R₂`, and `(2, 2)` is generically stable iff `R₂ ≥ R₁`.

**Formalization Note.** The game is stated in the paper's normal form ("Without loss of generality we
may write `Γ` in the form", p. 70); any `2 × 2` game with two strict pure equilibria is of this form
after relabelling strategies. Paper strategies `1, 2` are `0, 1 : Fin 2`. "`(2, 2)` weakly risk
dominates `(1, 1)` if `R₂ ≥ R₁`" is the symmetric reading the page leaves implicit. Generic stability
(`IsGenericallyStable`) is defined from the stationary distributions of the actual perturbed process
for every best-reply distribution and every admissible experimentation, with `L_Γ` computed from the
game (it equals `1` here, milestone `two_by_two_structure`), not from `R₁, R₂`. -/
theorem theorem_3 (a b : Fin 2 → Fin 2 → ℝ) (hab : IsNormalForm a b) :
    (IsGenericallyStable (payoff2x2 a b) profile11 ↔ R2 a b ≤ R1 a b) ∧
    (IsGenericallyStable (payoff2x2 a b) profile22 ↔ R1 a b ≤ R2 a b) := by sorry

end YoungConventions.RiskDominance
