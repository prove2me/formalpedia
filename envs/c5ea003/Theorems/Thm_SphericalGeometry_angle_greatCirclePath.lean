-- Prove2me | Theorems.Thm_SphericalGeometry_angle_greatCirclePath
-- name    : SphericalGeometry.angle_greatCirclePath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:14:28.17851+00:00
-- url     : https://prove2.me/theorems/3c9a60aa-57ef-4ce8-ab99-0d42ade6fa7f
-- title:
--   A great circle has unit speed for the angular metric
-- statement:
--   Let $v_1,v_2$ be an orthonormal pair in a real inner product space and $c$ the great circle through them. If $|s-t|\le\pi$ then
--
--   $$
--   \angle\bigl(c(s),c(t)\bigr)=|s-t| .
--   $$
--
--   **Role.** The angular metric $\angle(x,y)$ on the unit sphere is its intrinsic metric: the length of the shortest arc joining two unit vectors. The theorem says that a great circle, parametrized as above, is an isometric embedding of every interval of length at most $\pi$ into the sphere with that metric — that is, a *unit-speed geodesic*. This is the precise sense in which great circles are the geodesics of the sphere, and it is why the parameter of a closed spherical geodesic can be identified with arclength when one counts how many times it wraps.
--
--   The restriction $|s-t|\le\pi$ is necessary and not a technical artifact: beyond half a turn the two points are joined by a shorter arc on the other side, and the angle stops growing with the parameter. This is exactly the local, rather than global, character of a closed geodesic.
-- source:
--   Standard spherical geometry; the great-circle facts are the content of the lift used in Lemma 4.6 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4 (Spherical Billiards). Mathlib has no parametrized great circle and no geodesics of a sphere.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

theorem angle_greatCirclePath {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (s t : ℝ) (hst : |s - t| ≤ Real.pi) :
    InnerProductGeometry.angle (greatCirclePath v1 v2 s) (greatCirclePath v1 v2 t)
      = |s - t| := by sorry

end SphericalGeometry
