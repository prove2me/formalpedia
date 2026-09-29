-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_aFun_props
-- name    : ZhengQR.EOQHeuristic.aFun_props
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:45:20.227755+00:00
-- url     : https://prove2.me/theorems/48f71daa-b6de-4a80-9a51-3652c4fefeb9
-- title:
--   Lemma 6 — $A$ is increasing and convex, $Q^*$ exists uniquely, $Q = Q^* \iff A(Q) = \lambda K$, comparative statics in $K$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $H$ be as in Eq. (6) and
--
--   $$A(Q) = Q\,H(Q) - \int_0^Q H(y)\,dy. \qquad (9)$$
--
--   Then:
--
--   1. $A$ is strictly increasing on $[0, \infty)$;
--   2. $A$ is convex on $[0, \infty)$;
--   3. there is exactly one optimal order quantity $Q^* > 0$;
--   4. for every $Q > 0$, $Q$ is the optimal order quantity if and only if
--   $$A(Q) = \lambda K; \qquad (10)$$
--   5. for $0 < K < K'$, the optimal order quantities $Q^*(K)$, $Q^*(K')$ satisfy $Q^*(K) < Q^*(K')$, and the optimal reorder points satisfy $r^*(K') < r^*(K)$, where $r^* = r(Q^*)$.
--
--   Geometrically, $A(Q)$ is the area between the horizontal chord at height $H(Q)$ and the graph of $G$ over the optimal cycle, and the optimal order quantity is where that area equals $\lambda K$.
--
--   **Formalization Note** The paper states "$Q^*$ is increasing and $r^*$ (the optimal reorder point) is decreasing in $K$"; both are read as strict (the proof combines the strict monotonicity of $A$ with Lemma 3 part 3). "The optimal order quantity" is read as existence and uniqueness (item 3), which the paper presupposes when it names $Q^*$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 92, Lemma 6 and Eqs. (9)–(10)

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem aFun_props {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    StrictMonoOn (aFun (newsvendorCost μ h p) lam K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (aFun (newsvendorCost μ h p) lam K) ∧
    (∃! Q : ℝ, IsOptQty (newsvendorCost μ h p) lam K Q) ∧
    (∀ Q : ℝ, 0 < Q → (IsOptQty (newsvendorCost μ h p) lam K Q ↔ aFun (newsvendorCost μ h p) lam K Q = lam * K)) ∧
    (∀ K' : ℝ, K < K' → ∀ Q Q' : ℝ,
      IsOptQty (newsvendorCost μ h p) lam K Q → IsOptQty (newsvendorCost μ h p) lam K' Q' →
        Q < Q' ∧ reorderPt (newsvendorCost μ h p) lam K' Q' < reorderPt (newsvendorCost μ h p) lam K Q) := by sorry

end ZhengQR.EOQHeuristic
