-- Prove2me | Theorems.Thm_MetricGeometry_exists_unique_nearest_of_isNPC
-- name    : MetricGeometry.exists_unique_nearest_of_isNPC
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T20:54:47.796759+00:00
-- url     : https://prove2.me/theorems/c22065d7-97cf-4f54-8cc3-084a55e99ec1
-- title:
--   Projection onto a complete convex subset of a $\mathrm{CAT}(0)$ space
-- statement:
--   Let $X$ be a complete metric space in which every pair of points has a midpoint and which satisfies the CN inequality of Bruhat and Tits. Let $C\subseteq X$ be nonempty, closed, and closed under midpoints. Then every point $x\in X$ has a unique nearest point in $C$:
--
--   $$
--   \exists!\,p\in C \quad\text{with}\quad d(x,p)=\inf_{q\in C} d(x,q).
--   $$
--
--   This is the projection theorem for $\mathrm{CAT}(0)$ spaces. In a Hilbert space it is the classical statement that a nonempty closed convex set has a unique nearest point, from which orthogonal projection is built; here the linear structure is absent and the curvature condition does the same work.
--
--   **The mechanism.** The curvature condition converts the infimum into a Cauchy estimate. For $u,v\in C$, their midpoint again lies in $C$ and so is no closer to $x$ than the infimum $d$; feeding that into the CN inequality gives
--
--   $$
--   d(u,v)^2\;\le\;2\,d(x,u)^2+2\,d(x,v)^2-4d^2 .
--   $$
--
--   Along a minimizing sequence the right-hand side tends to $0$, so the sequence is Cauchy; completeness supplies a limit, closedness places it in $C$, and continuity of the distance shows it realizes the infimum. The same inequality applied to two minimizers gives $d(u,v)^2\le 0$, which is uniqueness.
--
--   That single inequality is the whole content: it is what fails in a positively curved space, where nearest points need not be unique, and what makes the argument independent of any linear structure.
-- source:
--   Synthetic metric geometry of nonpositively curved spaces. See M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Proposition II.2.4 (projection onto a complete convex subset of a CAT(0) space) and Chapter II.1 for convexity of the metric. The curvature hypothesis is the CN inequality of F. Bruhat and J. Tits, Groupes reductifs sur un corps local I, Publications Mathematiques de l'IHES 41 (1972), Section 3.2 (Un lemme de point fixe). Mathlib has the projection theorem only for Hilbert spaces and no synthetic curvature condition.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

open Filter Topology

theorem exists_unique_nearest_of_isNPC {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hnpc : IsNPC X) (hmid : HasMidpoints X)
    (C : Set X) (hC : IsClosed C) (hCne : C.Nonempty)
    (hconv : ∀ u ∈ C, ∀ v ∈ C, ∀ m, IsMidpoint m u v → m ∈ C)
    (x : X) :
    ∃ p, p ∈ C ∧ (∀ q ∈ C, dist x p ≤ dist x q) ∧
      ∀ p', p' ∈ C → (∀ q ∈ C, dist x p' ≤ dist x q) → p' = p := by sorry

end MetricGeometry
