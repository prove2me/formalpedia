-- Prove2me | Theorems.Thm_ZeroOneIALM_isolated_clusterPt_tendsto
-- name    : ZeroOneIALM.isolated_clusterPt_tendsto
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:27:54.021509+00:00
-- url     : https://prove2.me/theorems/4f7ec550-589d-4e84-8063-9e248a9c3b8f
-- title:
--   Kanzow–Qi: vanishing steps and an isolated accumulation point give convergence
-- statement:
--   Let $\{x^k\}_{k\in\mathbb N}$ be a sequence in a proper metric space, for instance $\mathbb R^m$, with $\mathrm{dist}(x^{k+1},x^k)\to0$. If $x^*$ is an accumulation point of the sequence and is isolated, that is, some ball around $x^*$ contains no other accumulation point, then $x^k\to x^*$.
--
--   This is the result of Kanzow and Qi that the proof of Theorem 7 invokes without restating. Local compactness of the space is needed: the statement fails in infinite dimension.
--
--   Differences from the source:
--   - generalization: sequences in Euclidean space → sequences in a proper metric space; reason: Euclidean spaces and their finite products are proper
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, proof of Theorem 7, p.26, citing Kanzow and Qi [22]; also p.20, citing [22, Proposition 7]

import Mathlib

open Filter Topology

namespace ZeroOneIALM

/-- The result of Kanzow and Qi (A QP-free constrained Newton-type method for variational inequality
problems, Math. Programming 85 (1999)) invoked in the proof of Theorem 7, Zhang & Xiu,
arXiv:2112.00440v1, p.26: if the distance between successive terms of a sequence tends to `0` and
`xstar` is an isolated accumulation point of the sequence, then the whole sequence converges to
`xstar`.

**Formalization Note.** The paper cites the result without restating it, for sequences in Euclidean
space. It is stated here for a proper metric space, which covers `ℝᵖ × ℝⁿ × ℝⁿ`. Isolation means that
some ball around `xstar` contains no other accumulation point. -/
theorem isolated_clusterPt_tendsto {X : Type*} [MetricSpace X] [ProperSpace X]
    {x : ℕ → X} {xstar : X}
    (hstep : Tendsto (fun k => dist (x (k + 1)) (x k)) atTop (𝓝 0))
    (hcluster : MapClusterPt xstar atTop x)
    (hisolated : ∃ δ : ℝ, 0 < δ ∧ ∀ y, MapClusterPt y atTop x → dist y xstar < δ → y = xstar) :
    Tendsto x atTop (𝓝 xstar) := by sorry

end ZeroOneIALM
