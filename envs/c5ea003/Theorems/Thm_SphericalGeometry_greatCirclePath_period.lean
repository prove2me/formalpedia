-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_period
-- name    : SphericalGeometry.greatCirclePath_period
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:14:37.693282+00:00
-- url     : https://prove2.me/theorems/778becf8-6b4e-4889-b44c-5c1e660cf595
-- title:
--   A great circle closes only at multiples of $2\pi$
-- statement:
--   Let $v_1,v_2$ be an orthonormal pair in a real inner product space and $c$ the great circle through them. If $c(T)=c(0)$ then
--
--   $$
--   T=2\pi n\qquad\text{for some }n\in\mathbb Z .
--   $$
--
--   **Role.** This is the quantization statement behind every counting argument about closed spherical geodesics: a great circle has length exactly $2\pi$, so a closed unit-speed geodesic of the sphere runs through a whole number of full turns and nothing in between. Combined with the fact that a closed billiards path in a spherical Coxeter chamber lifts to a great circle, and that the lift is shifted by a Weyl group element whose order $k$ divides $|W|$, it is what turns the period $\lambda$ of the billiards path into a rational multiple $2\pi j/k$ of a full turn — the arithmetic constraint that ultimately bounds the denominators of the orders of harmonic maps into a Euclidean building.
--
--   Only the closing condition at a single parameter is needed; periodicity as a function is not assumed.
-- source:
--   Standard spherical geometry; the great-circle facts are the content of the lift used in Lemma 4.6 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4 (Spherical Billiards). Mathlib has no parametrized great circle and no geodesics of a sphere.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

theorem greatCirclePath_period {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0) (T : ℝ)
    (hT : greatCirclePath v1 v2 T = greatCirclePath v1 v2 0) :
    ∃ n : ℤ, T = n * (2 * Real.pi) := by sorry

end SphericalGeometry
