-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_resistance_h2_to_h1
-- name    : YoungConventions.RiskDominance.resistance_h2_to_h1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:05:05.053418+00:00
-- url     : https://prove2.me/theorems/36f7d553-4b4e-4ea6-88b4-2f0c117fa526
-- title:
--   Resistance from $h_2$ to $h_1$ is $\lceil R_2k\rceil$
-- statement:
--   Let $\Gamma$ be a $2\times2$ game in normal form, $k\ge1$ and $3k\le m$. Then the least total resistance (number of mistakes) of a path of successor states from $h_2=((2,2),\dots,(2,2))$ to $h_1=((1,1),\dots,(1,1))$ is
--   $$r_{21}=\lceil R_2k\rceil,\qquad R_2=\min\Big\{\frac{a_{22}-a_{12}}{a_{11}-a_{12}-a_{21}+a_{22}},\ \frac{b_{22}-b_{21}}{b_{11}-b_{12}-b_{21}+b_{22}}\Big\}.$$
--
--   **Formalization Note** As for $r_{12}$: both inequalities are claimed, and "$m/k$ large enough" is taken as $3k\le m$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_classResistance
import Definitions.Def_YoungConventions_RiskDominance_convention
import Definitions.Def_YoungConventions_RiskDominance_Strat2
import Definitions.Def_YoungConventions_RiskDominance_payoff2x2
import Definitions.Def_YoungConventions_RiskDominance_IsNormalForm
import Definitions.Def_YoungConventions_RiskDominance_R2
import Definitions.Def_YoungConventions_RiskDominance_profile11
import Definitions.Def_YoungConventions_RiskDominance_profile22

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **Resistance from `h₂` to `h₁` is `⌈R₂k⌉`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72 (PDF p. 17): "A similar argument shows that the resistance in going from `h₂` to `h₁` is `[R₂k]` where `R₂ = min{{ (a₂₂ − a₁₂)/(a₁₁ − a₁₂ − a₂₁ + a₂₂), (b₂₂ − b₂₁)/(b₁₁ − b₁₂ − b₂₁ + b₂₂) }}`."

For a `2 × 2` game in normal form, `1 ≤ k` and `3k ≤ m`, the least total number of mistakes on a
path of successor steps from `h₂` to `h₁` equals `⌈R₂ k⌉`.

**Formalization Note.** `[x]` is the ceiling (`⌈·⌉₊`, the natural-number ceiling; `R₂k > 0`). Both
inequalities are claimed: the page exhibits a path with `⌈R₂k⌉` mistakes (Table 1, which needs
`m/k` large enough: "It suffices that `m ≥ 2k`" for the first stage) and asserts that no path has
fewer. The page's "`m/k` is large enough" is taken as `3k ≤ m`, the regime `k ≤ m/(L_Γ + 2)` of
Theorem 3 with `L_Γ = 1`. Ties in a best reply count as best replies (p. 71: "If equality holds in
(5) then strategy 2 is among Column's best replies"), which is why the ceiling is exact. -/
theorem resistance_h2_to_h1 (a b : Fin 2 → Fin 2 → ℝ) (hab : IsNormalForm a b)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : 3 * k ≤ m) :
    classResistance (payoff2x2 a b) k {convention (m := m) profile22} {convention (m := m) profile11} =
      ⌈R2 a b * k⌉₊ := by sorry

end YoungConventions.RiskDominance
