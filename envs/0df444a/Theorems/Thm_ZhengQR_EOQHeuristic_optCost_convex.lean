-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_optCost_convex
-- name    : ZhengQR.EOQHeuristic.optCost_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:43:38.505563+00:00
-- url     : https://prove2.me/theorems/424d6134-befe-4c8d-8cf2-c939a0c3ac13
-- title:
--   Lemma 5 — $C(Q) = c(Q, r(Q))$ is convex on $Q > 0$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), the average cost with the reorder point chosen optimally,
--
--   $$C(Q) = c(Q, r(Q)),$$
--
--   is a convex function of the order quantity $Q$ on $(0, \infty)$.
--
--   Convexity of $C$ makes the first-order condition (8) necessary and sufficient for the optimal order quantity.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Lemma 5

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem optCost_convex {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ConvexOn ℝ (Set.Ioi 0) (optCost (newsvendorCost μ h p) lam K) := by sorry

end ZhengQR.EOQHeuristic
