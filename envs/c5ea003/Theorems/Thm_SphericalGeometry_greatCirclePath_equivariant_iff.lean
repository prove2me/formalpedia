-- Prove2me | Theorems.Thm_SphericalGeometry_greatCirclePath_equivariant_iff
-- name    : SphericalGeometry.greatCirclePath_equivariant_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T11:24:36.199145+00:00
-- url     : https://prove2.me/theorems/69d58a31-67dc-4634-bdd4-85cd182cb15f
-- title:
--   Shift equivariance of a great circle is rotation of its frame
-- statement:
--   A linear isometry $w$ realizes the shift by $T$ along the great circle spanned by $v_1,v_2$ — that is,
--   $$\gamma_{v_1,v_2}(s+T)=w\cdot\gamma_{v_1,v_2}(s)\quad\text{for every }s$$
--   — if and only if $w$ rotates the naming frame through the angle $T$:
--   $$w v_1=\gamma_{v_1,v_2}(T),\qquad w v_2=\gamma_{v_2,-v_1}(T).$$
--
--   **Role.** Statements about closed billiards paths are phrased as an equivariance of *paths*: the great circle, advanced by a fixed angle, is carried onto itself by an element of the finite Weyl group. This equivalence replaces that condition by two equations on vectors, so that the Weyl element is pinned down by its action on a single orthonormal frame. It is the bridge between the geometric statement — a closed path in the spherical Coxeter complex — and the arithmetic one: since $w$ lies in a finite group, the angle $T$ it realizes is a rational multiple of $2\pi$ whose denominator divides the order of $w$, which is how the constraint on the possible orders of a harmonic map is finally read off.
--
--   **Proof.** For the forward direction, evaluate the equivariance at $s=0$, where $\gamma_{v_1,v_2}(0)=v_1$, to get the first equation; and at $s=\pi/2$, where $\gamma_{v_1,v_2}(\pi/2)=v_2$ while the left-hand side, rewritten by the shift identity, is the second vector of the rotated frame, to get the second. Conversely, the shift identity presents $\gamma_{v_1,v_2}(\cdot+T)$ as the great circle named by the rotated frame, and transport under a linear isometry presents $w\circ\gamma_{v_1,v_2}$ as the one named by $(w v_1,w v_2)$; the two hypotheses say those frames agree.
--
--   **Formalization note.** Orthonormality of $v_1,v_2$ is not needed for either direction: the equivalence is an identity of formal linear combinations. It is only when one wants the two frames to name genuine great circles that orthonormality enters, and that is recorded separately.
-- source:
--   The reduction underlying the closed-billiards-path analysis of Section 3 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem greatCirclePath_equivariant_iff {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w : E ≃ₗᵢ[ℝ] E) (v1 v2 : E) (T : ℝ) :
    (∀ s : ℝ, greatCirclePath v1 v2 (s + T) = w (greatCirclePath v1 v2 s))
      ↔ (w v1 = greatCirclePath v1 v2 T
          ∧ w v2 = greatCirclePath v2 (-v1) T) := by sorry

end SphericalGeometry
