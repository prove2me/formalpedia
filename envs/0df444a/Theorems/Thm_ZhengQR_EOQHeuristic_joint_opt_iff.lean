-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_joint_opt_iff
-- name    : ZhengQR.EOQHeuristic.joint_opt_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:44:42.625563+00:00
-- url     : https://prove2.me/theorems/23fd633f-a431-4772-bf27-5df6d538fde3
-- title:
--   Theorem 1 — $(Q, r)$ is optimal iff $c(Q, r) = G(r) = G(r + Q)$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $Q > 0$ and $r \in \mathbb{R}$. Then $(Q, r)$ minimises $c$ over $\{Q' > 0\} \times \mathbb{R}$ if and only if
--
--   $$c(Q, r) = G(r) = G(r + Q).$$
--
--   The theorem characterises the optimal policy by two simultaneous equations; the paper uses it to derive qualitative properties of $(Q, r)$ systems.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 92, Theorem 1

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem joint_opt_iff {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q r : ℝ) (hQ : 0 < Q) :
    (∀ Q' r' : ℝ, 0 < Q' → qrCost (newsvendorCost μ h p) lam K Q r ≤ qrCost (newsvendorCost μ h p) lam K Q' r') ↔
      (qrCost (newsvendorCost μ h p) lam K Q r = newsvendorCost μ h p r ∧ newsvendorCost μ h p r = newsvendorCost μ h p (r + Q)) := by sorry

end ZhengQR.EOQHeuristic
