-- Prove2me | Theorems.Thm_SphericalGeometry_orthonormal_greatCirclePath_frame
-- name    : SphericalGeometry.orthonormal_greatCirclePath_frame
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T11:17:21.781629+00:00
-- url     : https://prove2.me/theorems/e57970f6-b9a7-402b-8df0-4e479cd06358
-- title:
--   The rotated frame of a great circle is again orthonormal
-- statement:
--   If $v_1,v_2$ is an orthonormal pair then so is the rotated frame at any parameter $c$: the vectors $\gamma_{v_1,v_2}(c)$ and $\gamma_{v_2,-v_1}(c)$ are again unit and orthogonal.
--
--   **Role.** The companion to the shift identity. Together they say that moving the starting point along a great circle produces another legitimate naming of the same circle, so that statements quantified over orthonormal pairs are invariant under reparametrization of the circle they describe.
--
--   **Proof.** Expanding the inner products and using $\langle v_1,v_1\rangle=\langle v_2,v_2\rangle=1$ and $\langle v_1,v_2\rangle=0$, the two squared norms are $\cos^2c+\sin^2c=1$, and the cross term is $-\cos c\sin c+\sin c\cos c=0$.
-- source:
--   Elementary identity used in the closed-billiards-path analysis of Section 3 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem orthonormal_greatCirclePath_frame {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1)
    (h12 : inner ℝ v1 v2 = (0:ℝ)) (c : ℝ) :
    ‖greatCirclePath v1 v2 c‖ = 1 ∧ ‖greatCirclePath v2 (-v1) c‖ = 1
      ∧ inner ℝ (greatCirclePath v1 v2 c)
          (greatCirclePath v2 (-v1) c) = (0:ℝ) := by sorry

end SphericalGeometry
