-- Prove2me | Theorems.Thm_InnerProductGeometry_exists_mem_segment_angle_eq
-- name    : InnerProductGeometry.exists_mem_segment_angle_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T00:48:24.825739+00:00
-- url     : https://prove2.me/theorems/ab9347e2-66a9-451b-95bb-fb595cbeb1e5
-- title:
--   Every intermediate angle is realised on the segment between two vectors
-- statement:
--   Let $V$ be a real inner product space and let $b,c\in V$ be nonzero vectors that are not opposite, i.e. the
--   angle $\angle(b,c)$ is not $\pi$. Then every intermediate value of the angle is realised by a vector on the
--   segment joining $b$ to $c$: for each $\theta$ with $0\le\theta\le\angle(b,c)$ there is a point
--
--   $$x\in[b,c]=\{(1-\lambda)b+\lambda c:\lambda\in[0,1]\},\qquad x\neq 0,$$
--
--   such that
--
--   $$\angle(b,x)=\theta,\qquad \angle(x,c)=\angle(b,c)-\theta,\qquad \|x\|\le\max(\|b\|,\|c\|).$$
--
--   **Role.** This is the sweeping construction that lets an angle at a vertex be split into two prescribed parts.
--   Given a Euclidean triangle with apex at the origin and opposite side $[b,c]$, moving a point along that side
--   sweeps the ray from the origin continuously from the direction of $b$ to the direction of $c$, so any
--   intermediate opening angle occurs; and because the ray meets the side, the two partial angles add up exactly
--   to the whole rather than merely satisfying the triangle inequality. The norm bound records that the sweeping
--   point never leaves the disc spanned by the two endpoints, so a length constraint imposed on $b$ and $c$ is
--   inherited by $x$.
--
--   Both features are what the classical proof that the Alexandrov angle between geodesics satisfies the triangle
--   inequality needs: it argues by contradiction from an apex angle strictly larger than the sum of two others,
--   splits that apex angle at an interior point of the opposite side into two pieces each still too large, and
--   uses the norm bound to keep the new point inside the range where the defining $\limsup$ estimates apply.
--
--   The hypothesis $\angle(b,c)\neq\pi$ cannot be dropped: it is exactly the condition that the origin does not lie
--   on the segment $[b,c]$, and the angle at the origin is undefined there.
--
--   **Formalization Note.** `angle` is `InnerProductGeometry.angle`, the unoriented angle
--   $\arccos\bigl(\langle x,y\rangle/(\|x\|\|y\|)\bigr)\in[0,\pi]$ between two vectors, and `segment ℝ b c` is
--   Mathlib's convex segment.
-- source:
--   The Euclidean construction used in the proof of Proposition I.1.14 (the triangle inequality for Alexandrov angles) in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles): 'enables us to choose a point x in [x', x''] such that the angle a' (resp. a'') between the Euclidean segments [0, x'] and [0, x] (resp. [0, x''] and [0, x]) is bigger than ...'.

import Mathlib

namespace InnerProductGeometry

theorem exists_mem_segment_angle_eq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b c : V) (hb : b ≠ 0) (hc : c ≠ 0)
    (hpi : angle b c ≠ Real.pi) (θ : ℝ) (h0 : 0 ≤ θ) (hle : θ ≤ angle b c) :
    ∃ x ∈ segment ℝ b c, x ≠ 0 ∧ angle b x = θ ∧
      angle x c = angle b c - θ ∧ ‖x‖ ≤ max ‖b‖ ‖c‖ := by sorry

end InnerProductGeometry
