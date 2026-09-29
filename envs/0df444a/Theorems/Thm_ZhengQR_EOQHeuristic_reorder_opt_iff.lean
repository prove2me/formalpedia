-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_reorder_opt_iff
-- name    : ZhengQR.EOQHeuristic.reorder_opt_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:40:53.79899+00:00
-- url     : https://prove2.me/theorems/ffc7fb14-6c28-4b58-9a8e-60f8a3c2762b
-- title:
--   Lemma 2 — for $Q > 0$, $r$ is an optimal reorder point iff $G(r) = G(r + Q)$
-- statement:
--   In the stochastic $(Q, r)$ model (demand rate $\lambda > 0$, leadtime $L > 0$, cost rates $h, p > 0$, nonnegative leadtime demand with mean $\lambda L$, newsvendor cost $G$ with a unique minimiser, fixed ordering cost $K > 0$), fix an order quantity $Q > 0$. Then $c(Q,\cdot)$ has a minimiser, and for every $r \in \mathbb{R}$,
--
--   $$r \text{ minimises } c(Q, \cdot) \iff G(r) = G(r + Q).$$
--
--   In words: for a given order quantity, the reorder point is optimal exactly when the inventory costs at the start and at the end of a replenishment cycle are equal.
--
--   **Formalization Note** The paper writes "$r = r(Q)$ if and only if $G(r) = G(r+Q)$", where $r(Q)$ is an optimal reorder point for $Q$. The statement is formalised for the minimiser predicate, and the existence of a minimiser, which the paper presupposes, is added as a conjunct.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 90, Lemma 2

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem reorder_opt_iff {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    (∃ r : ℝ, IsOptReorder (newsvendorCost μ h p) lam K Q r) ∧
      ∀ r : ℝ, IsOptReorder (newsvendorCost μ h p) lam K Q r ↔ newsvendorCost μ h p r = newsvendorCost μ h p (r + Q) := by sorry

end ZhengQR.EOQHeuristic
