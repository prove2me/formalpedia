-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_shift_rational_of_finite
-- name    : SphericalGeometry.greatCirclePath_shift_rational_of_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:47:46.41922+00:00
-- url     : https://prove2.me/theorems/2f2866d6-bcc0-4d9f-a026-e1b81b8cc674
-- title:
--   A great-circle parameter shift realised by a finite isometry group is a rational multiple of a turn
-- statement:
--   Let $E$ be a real inner product space, let $v_1,v_2\in E$ be an orthonormal pair, and let
--   $$\gamma(s)=\cos(s)\,v_1+\sin(s)\,v_2$$
--   be the unit-speed great circle they span. Let $G$ be a **finite** group of linear isometries of $E$, and suppose some $w\in G$ realises a shift of the parameter by $c$ along $\gamma$:
--   $$\gamma(s+c)=w\bigl(\gamma(s)\bigr)\qquad\text{for every }s\in\mathbb{R}.$$
--   Then the shift is a rational multiple of a full turn, with a denominator controlled by the group: there are $k\in\mathbb{N}$ with $0<k$ and $k\mid |G|$, and $n\in\mathbb{Z}$, such that
--   $$k\,c=2\pi n.$$
--
--   **Role.** This is the mechanism that forces the order of a harmonic map into a Euclidean building to be rational with denominator dividing the order of the Weyl group. A homogeneous harmonic map sends the unit circle of the plane to a closed billiards path in the spherical building; on each straight stretch that path is a great circle arc, and the passage from one stretch to the next is realised by an element of the (finite) Weyl group. The identity above says exactly that the total angle advanced is reproduced by a group element, and the conclusion converts that into the arithmetic statement $\alpha=m/k$ with $k$ dividing the order of the group. Nothing about buildings is used: only that the group is finite.
--
--   **Formalization note.** $G$ is taken to be a subgroup of the group of linear isometric automorphisms of $E$ carrying a `Fintype` instance, and $|G|$ is its cardinality; the Weyl group of a Euclidean Coxeter datum is such a subgroup. The number $k$ produced is the order of $w$, which divides $|G|$ by Lagrange's theorem.
-- source:
--   The rationality of the order in Theorem 2.15 (angle rigidity and closed billiards paths) of A. Breiner and A. Dees, Harmonic maps into Euclidean buildings, arXiv:2604.16608; the underlying periodicity argument is that of B. Kleiner and B. Leeb, Rigidity of quasi-isometries for symmetric spaces and Euclidean buildings, Publ. Math. IHES 86 (1997), Section 4.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem greatCirclePath_shift_rational_of_finite {E : Type u}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : Subgroup (E ≃ₗᵢ[ℝ] E)) [Fintype G]
    (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1) (ho : inner ℝ v1 v2 = 0)
    (w : G) (c : ℝ)
    (hc : ∀ s : ℝ, greatCirclePath v1 v2 (s + c)
      = (w : E ≃ₗᵢ[ℝ] E) (greatCirclePath v1 v2 s)) :
    ∃ k : ℕ, 0 < k ∧ k ∣ Fintype.card G ∧
      ∃ n : ℤ, (k : ℝ) * c = (n : ℝ) * (2 * Real.pi) := by sorry

end SphericalGeometry
