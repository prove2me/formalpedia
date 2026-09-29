-- Prove2me | Theorems.Thm_InnerProductGeometry_exists_pair_norm_eq_angle_eq
-- name    : InnerProductGeometry.exists_pair_norm_eq_angle_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T00:52:14.984351+00:00
-- url     : https://prove2.me/theorems/209dd886-0221-43ae-8377-d8e2e239e634
-- title:
--   Two lengths and an included angle are realised in the Euclidean plane
-- statement:
--   Two prescribed positive lengths and a prescribed angle in $[0,\pi]$ are always realised by a pair of vectors in
--   the Euclidean plane: for all $t,s>0$ and $\alpha\in[0,\pi]$ there are $b,c\in\mathbb{C}$ with
--
--   $$\|b\|=t,\qquad \|c\|=s,\qquad \angle(b,c)=\alpha.$$
--
--   **Role.** Comparison geometry proceeds by replacing a configuration in an abstract metric space by a Euclidean
--   model with the same measurements and then reasoning inside the model. This statement supplies the models. It is
--   the "two sides and the included angle" construction: unlike the construction of a comparison triangle from three
--   side lengths, which needs the triangle inequality as a hypothesis, prescribing two sides and the angle between
--   them is unconditionally possible, and the third side is then whatever the law of cosines makes it. That is the
--   form needed when one wants to build a model triangle whose apex angle is chosen by hand — for instance an angle
--   strictly smaller than the comparison angle of a given triple, so that the model's third side is strictly shorter
--   than the original one.
--
--   The witnesses are $b=t$ and $c=s\cos\alpha+is\sin\alpha$. The Pythagorean identity gives $\|c\|=s$, the real
--   inner product of $b$ and $c$ is $ts\cos\alpha$, and since $\alpha\in[0,\pi]$ the arccosine recovers $\alpha$ from
--   its cosine.
--
--   **Formalization Note.** The plane is taken to be $\mathbb{C}$ with its standard real inner product structure, and
--   `angle` is `InnerProductGeometry.angle`, the unoriented angle between two vectors.
-- source:
--   The construction of the Euclidean model configuration in the proof of Proposition I.1.14 in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles): 'Consider a triangle in E^2 with vertices 0, x', x'' such that d(0, x') = t', d(0, x'') = t'', and such that the angle a at the vertex 0 satisfies ...'.

import Mathlib

namespace InnerProductGeometry

theorem exists_pair_norm_eq_angle_eq (t s α : ℝ) (ht : 0 < t) (hs : 0 < s)
    (h0 : 0 ≤ α) (hpi : α ≤ Real.pi) :
    ∃ b c : ℂ, ‖b‖ = t ∧ ‖c‖ = s ∧ angle b c = α := by sorry

end InnerProductGeometry
