-- Prove2me | Theorems.Thm_YukawaPotential_yukawaPotential_laplacian
-- name    : YukawaPotential.yukawaPotential_laplacian
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T13:28:45.583037+00:00
-- url     : https://prove2.me/theorems/989f3a37-270f-49a8-8cc6-5b2b4f81630e
-- title:
--   Yukawa potential solves the screened Poisson equation $\Delta\phi=(\alpha m)^2\phi$ away from the origin
-- statement:
--   Let $g,\alpha,m\in\mathbb R$ and consider the potential of a point source at the origin of $\mathbb R^3$,
--   $$\phi(x) = V(|x|) = -g^2\,\frac{e^{-\alpha m |x|}}{|x|}.$$
--   Then at every point $x\neq0$,
--   $$\Delta\phi(x) = (\alpha m)^2\,\phi(x),$$
--   where $\Delta=\partial_1^2+\partial_2^2+\partial_3^2$ is the Laplacian on $\mathbb R^3$.
--
--   This is the static, radial form $\nabla^2\phi=\mu^2\phi$ of the massive wave equation $\Box\phi+\mu^2\phi=0$ from the section *Relation to wave equation*, whose radial solutions are $\phi(r)=K e^{-\mu r}/r$; here $K=-g^2$ and $\mu=\alpha m$.
--
--   **Formalization Note** The Laplacian is Mathlib's `Laplacian.laplacian` on the inner-product space `EuclideanSpace ℝ (Fin 3)` (trace of the second Fréchet derivative). No sign condition on $\alpha m$ is needed.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Relation to wave equation': □φ + μ²φ = 0; for radial time-independent φ, ∇²φ = μ²φ, with solutions φ(r) = K e^{-μr}/r, 'which is the Yukawa potential'.

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawaPotential_laplacian (g α m : ℝ) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ≠ 0) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin 3) => yukawaPotential g α m ‖y‖) x =
      (α * m) ^ 2 * yukawaPotential g α m ‖x‖ := by sorry
end YukawaPotential
