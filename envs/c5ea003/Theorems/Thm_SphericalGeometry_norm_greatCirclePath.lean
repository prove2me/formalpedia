-- Prove2me | Theorems.Thm_SphericalGeometry_norm_greatCirclePath
-- name    : SphericalGeometry.norm_greatCirclePath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:14:16.64963+00:00
-- url     : https://prove2.me/theorems/3766486e-4f64-47a9-bbd1-f7c69b6d3fd0
-- title:
--   A great circle lies on the unit sphere
-- statement:
--   For an orthonormal pair $v_1,v_2$ in a real inner product space, every point of the great circle $c(s)=\cos(s)v_1+\sin(s)v_2$ is a unit vector:
--
--   $$
--   \|c(s)\|=1\qquad\text{for all }s\in\mathbb R .
--   $$
--
--   **Role.** This is the statement that the parametrization does what its name says: it traces a curve *on the sphere*, not merely in the plane spanned by $v_1$ and $v_2$. It is the Pythagorean identity $\cos^2 s+\sin^2 s=1$ read in the orthonormal frame $(v_1,v_2)$, and it is needed before the angle between two points of the curve can be computed at all, since the angle between two vectors is defined by dividing by the product of their norms.
-- source:
--   Standard spherical geometry; the great-circle facts are the content of the lift used in Lemma 4.6 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4 (Spherical Billiards). Mathlib has no parametrized great circle and no geodesics of a sphere.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

theorem norm_greatCirclePath {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (s : ℝ) :
    ‖greatCirclePath v1 v2 s‖ = 1 := by sorry

end SphericalGeometry
