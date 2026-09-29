-- Prove2me | Theorems.Thm_SphericalGeometry_lipschitzWith_smul_greatCirclePath
-- name    : SphericalGeometry.lipschitzWith_smul_greatCirclePath
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:25:35.495177+00:00
-- url     : https://prove2.me/theorems/24664de5-c433-43e6-8246-b42d08245ea8
-- title:
--   A great circle of radius L traversed at speed alpha is (L alpha)-Lipschitz
-- statement:
--   For an orthonormal pair $v_1,v_2$ and nonnegative reals $\alpha,L$, the curve
--   $$\theta\longmapsto L\bigl(\cos(\alpha\theta)v_1+\sin(\alpha\theta)v_2\bigr),$$
--   a great circle of radius $L$ on the sphere traversed at angular speed $\alpha$, is Lipschitz with constant $L\alpha$.
--
--   **Role.** This is the quantitative statement that such a curve moves at speed $L\alpha$, and it is the input to the length estimate for the image of a circle: composed with the bound "variation $\le$ Lipschitz constant times parameter length", it gives $\ell\le2\pi\alpha L$ over one full turn, which is the upper half of the length identity in the constant-distance branch of the order theorem.
--
--   **The argument.** Scaling multiplies distances by $L$, and along the great circle the chord is $2|\sin\frac{u-v}{2}|$; with $u=\alpha s$, $v=\alpha t$ and $|\sin x|\le|x|$ this is at most $\alpha|s-t|$. Hence the distance between the values at $s$ and $t$ is at most $L\alpha|s-t|$.
-- source:
--   The speed of the great circle appearing in Lemma 3.2 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, arXiv:2604.16608.

import Definitions.Def_spherical_great_circle

namespace SphericalGeometry

universe u

theorem lipschitzWith_smul_greatCirclePath {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v1 v2 : E) (h1 : ‖v1‖ = 1) (h2 : ‖v2‖ = 1)
    (ho : inner ℝ v1 v2 = 0) (alpha L : ℝ) (halpha : 0 ≤ alpha) (hL : 0 ≤ L) :
    LipschitzWith (Real.toNNReal (L * alpha))
      (fun theta : ℝ => L • greatCirclePath v1 v2 (alpha * theta)) := by sorry

end SphericalGeometry
