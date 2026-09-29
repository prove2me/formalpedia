-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_joint_convex
-- name    : ZhengQR.EOQHeuristic.joint_convex
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:40:03.96927+00:00
-- url     : https://prove2.me/theorems/862f241d-d576-472d-92cc-a8c648a6cf93
-- title:
--   Lemma 1 — $c(Q, r)$ is jointly convex in $Q > 0$ and $r$
-- statement:
--   Consider the stochastic $(Q, r)$ model with demand rate $\lambda>0$, leadtime $L>0$, holding and backorder cost rates $h, p > 0$, leadtime demand $D \ge 0$ with $E(D) = \lambda L$, newsvendor cost $G(y) = E[h(y-D)^+ + p(D-y)^+]$ with a unique minimiser, and fixed ordering cost $K > 0$. Then the average cost
--
--   $$c(Q, r) = \frac{\lambda K + \int_r^{r+Q} G(y)\,dy}{Q}$$
--
--   is a jointly convex function of $(Q, r)$ on the domain $\{Q > 0\} \times \mathbb{R}$.
--
--   Joint convexity is what makes sequential minimisation (first over $r$, then over $Q$) yield a convex function of $Q$ (Lemma 5).
--
--   **Formalization Note** The paper writes "a joint convex function of $Q$ and $r$" without naming the domain; $c$ is defined only for $Q > 0$, so the domain is $(0,\infty) \times \mathbb{R}$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 89, Lemma 1

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem joint_convex {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ))
      (fun z : ℝ × ℝ => qrCost (newsvendorCost μ h p) lam K z.1 z.2) := by sorry

end ZhengQR.EOQHeuristic
