-- Prove2me | Theorems.Thm_SphericalGeometry_eq_greatCirclePath_of_comparisonAngle
-- name    : SphericalGeometry.eq_greatCirclePath_of_comparisonAngle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:50:24.902652+00:00
-- url     : https://prove2.me/theorems/2b8dc039-42d4-4f3d-888d-2f63a0bb1844
-- title:
--   A curve of constant angular speed on a sphere is locally a great circle
-- statement:
--   Let $E$ be a real inner product space and let $\gamma:\mathbb{R}\to E$ lie on the sphere of radius $L>0$ about the origin and turn at constant angular speed $\alpha>0$ in the sense that
--   $$\widetilde\angle_0\bigl(\gamma(\theta_1),\gamma(\theta_2)\bigr)=\alpha\,|\theta_1-\theta_2|\qquad\text{whenever }|\theta_1-\theta_2|\le\delta,$$
--   where $\widetilde\angle_0$ is the comparison angle at the origin, and suppose $\alpha\delta<\pi$. Then near every parameter $\theta_0$ the curve is a great circle traversed at speed $\alpha$: there is an orthonormal pair $v_1,v_2$ with
--   $$\gamma(\theta)=L\bigl(\cos(\alpha(\theta-\theta_0))\,v_1+\sin(\alpha(\theta-\theta_0))\,v_2\bigr)\qquad\text{for }|\theta-\theta_0|\le\delta/2 .$$
--
--   **Role.** In a Euclidean building the image of the unit circle under a homogeneous harmonic map, when it lies at constant distance $L$ from the cone point, turns at constant angular speed there; inside a single apartment the ambient geometry is that of a Euclidean space, and the statement above says that such a curve is a great circle arc of the sphere of radius $L$. This is the concrete form of "a local geodesic of the space of directions lifts to a unit-speed geodesic of the model sphere", the step that converts the analytic input into the great-circle equivariance from which the rationality of the order is read off.
--
--   **The argument.** In a Euclidean space the comparison angle at the origin between two points of norm $L$ is the honest angle, and its cosine is the inner product divided by $L^{2}$; the arccosine is legitimate because the Cauchy–Schwarz inequality bounds that quotient by $1$. Rescaling by $L^{-1}$ and reparametrising by $\theta=\theta_0+s/\alpha$ produces a curve on the unit sphere with $\langle\eta(s),\eta(t)\rangle=\cos(s-t)$ whenever $|s-t|\le\alpha\delta$, and $\alpha\delta<\pi$ by hypothesis. A curve on the unit sphere satisfying that relation is locally a great circle; undoing the rescaling and the reparametrisation gives the displayed formula.
-- source:
--   The lift of a billiards path to a unit-speed geodesic of the model sphere, B. Kleiner and B. Leeb, Rigidity of quasi-isometries for symmetric spaces and Euclidean buildings, Publ. Math. IHES 86 (1997), Section 4; used in Section 4 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, arXiv:2604.16608.

import Definitions.Def_spherical_great_circle
import Definitions.Def_metric_geodesic_angle

namespace SphericalGeometry

open MetricGeometry

universe u

theorem eq_greatCirclePath_of_comparisonAngle {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (gamma : ℝ → E) (L alpha delta : ℝ) (hL : 0 < L)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hsmall : alpha * delta < Real.pi)
    (hsphere : ∀ theta : ℝ, ‖gamma theta‖ = L)
    (hangle : ∀ theta1 theta2 : ℝ, |theta1 - theta2| ≤ delta →
      comparisonAngle 0 (gamma theta1) (gamma theta2) = alpha * |theta1 - theta2|)
    (theta0 : ℝ) :
    ∃ v1 v2 : E, ‖v1‖ = 1 ∧ ‖v2‖ = 1 ∧ inner ℝ v1 v2 = 0 ∧
      ∀ theta : ℝ, |theta - theta0| ≤ delta / 2 →
        gamma theta = L • greatCirclePath v1 v2 (alpha * (theta - theta0)) := by sorry

end SphericalGeometry
