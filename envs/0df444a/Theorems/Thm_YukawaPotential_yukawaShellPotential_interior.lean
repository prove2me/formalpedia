-- Prove2me | Theorems.Thm_YukawaPotential_yukawaShellPotential_interior
-- name    : YukawaPotential.yukawaShellPotential_interior
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-03T15:25:04.050084+00:00
-- url     : https://prove2.me/theorems/bbc5d1a9-a517-4ed0-a158-c8e6d597bb1b
-- title:
--   Yukawa shell theorem, interior potential
-- statement:
--   Let $G,g\in\mathbb R$, $\alpha>0$, $m>0$, and let $V^{\mathrm{shell}}$ be the potential of a uniform thin spherical shell of radius $R$ and total scaling constant $G$ centred at the origin, felt by a point of scaling constant $g$ (see the definition item). For every $x\in\mathbb R^3$ with $0<|x|<R$,
--   $$V^{\mathrm{shell}}(x) = G\,g\,\frac{e^{-\alpha m R}}{R}\cdot\frac{\sinh(\alpha m |x|)}{\alpha m |x|}.$$
--
--   Unlike the Newtonian case, the interior potential is not constant.
--
--   **Formalization Note** The centre $x=0$ is excluded because the article's formula is there only defined as a limit ($\sinh(\alpha m r)/(\alpha m r)\to1$), while Lean would evaluate $\sinh(0)/0$ to $0$. The hypotheses force $R>0$.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Spherical shell': the interior potential is V(r < R) = G g (e^{-αmR}/R) (sinh αmr)/(αmr).

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawaShellPotential_interior (G g α m R : ℝ) (hα : 0 < α) (hm : 0 < m)
    (x : EuclideanSpace ℝ (Fin 3)) (hx0 : 0 < ‖x‖) (hx : ‖x‖ < R) :
    yukawaShellPotential G g α m R x =
      G * g * (Real.exp (-(α * m * R)) / R) * (Real.sinh (α * m * ‖x‖) / (α * m * ‖x‖)) := by sorry
end YukawaPotential
