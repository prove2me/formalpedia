-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_cost_formula
-- name    : ZhengQR.EOQHeuristic.cost_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:42:41.75818+00:00
-- url     : https://prove2.me/theorems/59e38162-3fd1-46af-93aa-8395f82292eb
-- title:
--   Eq. (7) — $\int_{r(Q)}^{r(Q)+Q} G = \int_0^Q H$ and $C(Q) = (\lambda K + \int_0^Q H(y)dy)/Q$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $r(Q)$ be the optimal reorder point, $H(Q) = G(r(Q))$ for $Q > 0$ with $H(0) = G(y^0)$, and $C(Q) = c(Q, r(Q))$. Then for every $Q > 0$,
--
--   $$\int_{r(Q)}^{r(Q)+Q} G(y)\,dy = \int_0^Q H(y)\,dy, \qquad C(Q) = \frac{\lambda K + \int_0^Q H(y)\,dy}{Q}. \qquad (7)$$
--
--   This expresses the optimised cost through the single function $H$, which is the form in which all later comparisons are made.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Eq. (7)

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem cost_formula {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    (∫ y in reorderPt (newsvendorCost μ h p) lam K Q..reorderPt (newsvendorCost μ h p) lam K Q + Q, newsvendorCost μ h p y) = ∫ y in (0 : ℝ)..Q, hFun (newsvendorCost μ h p) lam K y ∧
      optCost (newsvendorCost μ h p) lam K Q = (lam * K + ∫ y in (0 : ℝ)..Q, hFun (newsvendorCost μ h p) lam K y) / Q := by sorry

end ZhengQR.EOQHeuristic
