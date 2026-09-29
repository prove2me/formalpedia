-- Prove2me | Theorems.Thm_InnerProductGeometry_angle_triangle
-- name    : InnerProductGeometry.angle_triangle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:59:56.663572+00:00
-- url     : https://prove2.me/theorems/fa18be6d-60ff-4496-85d6-bc6d13107165
-- title:
--   The spherical triangle inequality for the unoriented angle
-- statement:
--   For nonzero vectors $x,y,z$ of a real inner product space, the unoriented angle satisfies the triangle inequality
--   $$\angle(x,z)\ \le\ \angle(x,y)+\angle(y,z).$$
--   Equivalently, the angle is a metric on the unit sphere — the round metric — and not merely a symmetric function.
--
--   **Role.** Mathlib defines the unoriented angle between two vectors and proves it symmetric, bounded by $\pi$, and compatible with positive rescaling, but not that it obeys the triangle inequality; without that the sphere is not known to be a metric space and no statement about spherical distances, geodesics or diameters can be made. It is needed here to show that the $\Delta_{\mathrm{mod}}$ distance — an infimum of angles over a finite group — is a metric, and more generally to treat the space of directions of a nonpositively curved space as a metric space.
--
--   **The argument.** Normalise the three vectors and consider the three unit-speed rays from the origin in their directions. The Alexandrov angle between two rays in an inner product space is the Euclidean angle between their directions, and the Alexandrov angle at a point obeys the triangle inequality for three unit-speed curves issuing from that point. Applying the latter with the ray in direction $y$ in the distinguished position and translating back through the former gives the assertion; the angle is unchanged by the normalisation because it is invariant under positive rescaling of either argument.
-- source:
--   The spherical triangle inequality; equivalently that the angular metric on the unit sphere is a metric, M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Grundlehren 319, Springer 1999, Part I, Chapter 1, Proposition 1.14 and Part II, Chapter 3.

import Definitions.Def_metric_alexandrov_angle

namespace InnerProductGeometry

universe u

theorem angle_triangle {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : E) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    InnerProductGeometry.angle x z
      ≤ InnerProductGeometry.angle x y + InnerProductGeometry.angle y z := by sorry

end InnerProductGeometry
