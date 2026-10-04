-- Prove2me | Theorems.Thm_YukawaPotential_yukawaShellPotential_exterior
-- name    : YukawaPotential.yukawaShellPotential_exterior
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-03T14:58:58.6332+00:00
-- url     : https://prove2.me/theorems/7362b8dd-c3ce-46e3-bb61-bd9ce3ab0c15
-- title:
--   Yukawa shell theorem, exterior: a shell acts as a point source of strength $G\,\sinh(\alpha mR)/(\alpha mR)$
-- statement:
--   Let $G,g\in\mathbb R$, $\alpha>0$, $m>0$, $R>0$, and let $V^{\mathrm{shell}}$ be the potential of a uniform thin spherical shell of radius $R$ and total scaling constant $G$ centred at the origin, felt by a point of scaling constant $g$ (see the definition item). For every $x\in\mathbb R^3$ with $|x|>R$,
--   $$V^{\mathrm{shell}}(x) = G\,g\,\frac{e^{-\alpha m|x|}}{|x|}\cdot\frac{\sinh(\alpha m R)}{\alpha m R}.$$
--
--   So outside the shell its potential equals that of a point source at the centre with magnitude $G\,\frac{\sinh \alpha mR}{\alpha mR}$, which is larger than $G$.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Spherical shell': V(r > R) = G g (e^{-αmr}/r) (sinh αmR)/(αmR).

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawaShellPotential_exterior (G g α m R : ℝ) (hα : 0 < α) (hm : 0 < m) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : R < ‖x‖) :
    yukawaShellPotential G g α m R x =
      G * g * (Real.exp (-(α * m * ‖x‖)) / ‖x‖) * (Real.sinh (α * m * R) / (α * m * R)) := by sorry
end YukawaPotential
