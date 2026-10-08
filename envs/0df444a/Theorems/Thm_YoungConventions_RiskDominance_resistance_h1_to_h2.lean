-- Prove2me | Theorems.Thm_YoungConventions_RiskDominance_resistance_h1_to_h2
-- name    : YoungConventions.RiskDominance.resistance_h1_to_h2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T18:03:35.330517+00:00
-- url     : https://prove2.me/theorems/a6afb63b-0c8b-4265-a5a6-e76f637aa0f5
-- title:
--   Resistance from $h_1$ to $h_2$ is $\lceil R_1k\rceil$
-- statement:
--   Let $\Gamma$ be a $2\times2$ game in normal form, $k\ge1$ and $3k\le m$. Then the least total resistance (number of mistakes) of a path of successor states from $h_1=((1,1),\dots,(1,1))$ to $h_2=((2,2),\dots,(2,2))$ is
--   $$r_{12}=\lceil R_1k\rceil,\qquad R_1=\min\Big\{\frac{a_{11}-a_{21}}{a_{11}-a_{12}-a_{21}+a_{22}},\ \frac{b_{11}-b_{12}}{b_{11}-b_{12}-b_{21}+b_{22}}\Big\},$$
--   where $\lceil x\rceil$ is the least integer greater than or equal to $x$.
--
--   **Formalization Note** Both inequalities are claimed: a path with $\lceil R_1k\rceil$ mistakes exists (Table 1), and none has fewer. The page's condition "$m/k$ is large enough" (with "It suffices that $m\ge2k$" for the first stage) is taken as $3k\le m$, the regime of Theorem 3. Ties count as best replies, which makes the ceiling exact.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, pp. 71–72, (5) and Table 1

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_classResistance
import Definitions.Def_YoungConventions_RiskDominance_convention
import Definitions.Def_YoungConventions_RiskDominance_Strat2
import Definitions.Def_YoungConventions_RiskDominance_payoff2x2
import Definitions.Def_YoungConventions_RiskDominance_IsNormalForm
import Definitions.Def_YoungConventions_RiskDominance_R1
import Definitions.Def_YoungConventions_RiskDominance_profile11
import Definitions.Def_YoungConventions_RiskDominance_profile22

open Filter Topology

namespace YoungConventions.RiskDominance

/-- **Resistance from `h₁` to `h₂` is `⌈R₁k⌉`.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, pp. 71–72 (PDF pp. 16–17): "For every real number `x`, let `[x]` denote the least integer greater than or equal to `x`. We have just shown that the resistance in going from `h₁` to `h₂` is `[R₁k]`." with `R₁` defined on p. 71

For a `2 × 2` game in normal form, `1 ≤ k` and `3k ≤ m`, the least total number of mistakes on a
path of successor steps from `h₁` to `h₂` equals `⌈R₁ k⌉`.

**Formalization Note.** `[x]` is the ceiling (`⌈·⌉₊`, the natural-number ceiling; `R₁k > 0`). Both
inequalities are claimed: the page exhibits a path with `⌈R₁k⌉` mistakes (Table 1, which needs
`m/k` large enough: "It suffices that `m ≥ 2k`" for the first stage) and asserts that no path has
fewer. The page's "`m/k` is large enough" is taken as `3k ≤ m`, the regime `k ≤ m/(L_Γ + 2)` of
Theorem 3 with `L_Γ = 1`. Ties in a best reply count as best replies (p. 71: "If equality holds in
(5) then strategy 2 is among Column's best replies"), which is why the ceiling is exact. -/
theorem resistance_h1_to_h2 (a b : Fin 2 → Fin 2 → ℝ) (hab : IsNormalForm a b)
    (k m : ℕ) [NeZero m] (hk : 1 ≤ k) (hkm : 3 * k ≤ m) :
    classResistance (payoff2x2 a b) k {convention (m := m) profile11} {convention (m := m) profile22} =
      ⌈R1 a b * k⌉₊ := by sorry

end YoungConventions.RiskDominance
