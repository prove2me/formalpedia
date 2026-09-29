-- Prove2me | Definitions.Def_spherical_great_circle
-- name    : spherical_great_circle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-27T23:12:49.465529+00:00
-- url     : https://prove2.me/theorems/81fb5112-996a-4b8c-949e-fed22dd25118
-- title:
--   Great circles of a real inner product space
-- statement:
--   A **great circle** of a real inner product space $E$ is the intersection of the unit sphere with a two-dimensional subspace. Given an orthonormal pair $v_1,v_2\in E$, the great circle through them is parametrized by arclength as
--
--   $$
--   c(s)=\cos(s)\,v_1+\sin(s)\,v_2 ,\qquad s\in\mathbb R .
--   $$
--
--   Every point of the curve is a unit vector, the inner product of two of its points is $\langle c(s),c(t)\rangle=\cos(s-t)$, and consequently the angle between them is exactly $|s-t|$ as long as that does not exceed $\pi$: the parameter *is* the arclength for the angular metric of the sphere.
--
--   **Role.** Great circles are the geodesics of the round sphere, and they are the objects a *billiards path* in a spherical Coxeter chamber lifts to. A closed billiards path in the model chamber $\Delta_{\mathrm{mod}}=\mathbb S^{N-1}/W$ — a unit-speed local geodesic that reflects off the walls — lifts to an honest unit-speed geodesic of $\mathbb S^{N-1}$, i.e. to a great circle, and the arithmetic of its period is then read off from the fact that a great circle closes up exactly at parameter $2\pi$. That is the mechanism by which a finite reflection group constrains the possible speeds of closed local geodesics in a spherical building, and hence the possible orders of harmonic maps into a Euclidean building.
--
--   Mathlib has spheres, orthonormal families and the angle between two vectors, but no parametrized great circle and no notion of a geodesic of a sphere.
-- source:
--   Standard spherical geometry. The role played here is that of the lift in Lemma 4.6 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608, Section 4 (Spherical Billiards). Mathlib has no parametrized great circle and no geodesics of a sphere.

import Mathlib

/-!
# Great circles of a real inner product space

A great circle is the unit-speed parametrization of the intersection of the
unit sphere with a two-dimensional subspace, written in terms of an
orthonormal pair spanning that subspace.  It is the model unit-speed geodesic
of the sphere, and the object a closed billiards path lifts to.

Mathlib has spheres, orthonormal families and the angle between two vectors,
but no parametrized great circle and nothing about geodesics of a sphere.
-/

namespace SphericalGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The great circle through the orthonormal pair `v1`, `v2`, parametrized by
arclength: at parameter `s` it is `cos s • v1 + sin s • v2`. -/
noncomputable def greatCirclePath (v1 v2 : E) : ℝ → E :=
  fun s => Real.cos s • v1 + Real.sin s • v2

end SphericalGeometry


