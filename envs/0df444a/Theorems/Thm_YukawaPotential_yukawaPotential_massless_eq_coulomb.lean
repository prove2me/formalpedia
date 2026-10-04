-- Prove2me | Theorems.Thm_YukawaPotential_yukawaPotential_massless_eq_coulomb
-- name    : YukawaPotential.yukawaPotential_massless_eq_coulomb
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T12:35:55.831331+00:00
-- url     : https://prove2.me/theorems/0d90dec2-eda9-468b-a68a-abecb1ba4708
-- title:
--   Massless Yukawa potential is the Coulomb potential
-- statement:
--   For all real $g$, $\alpha$ and $r$, the Yukawa potential with mass $m=0$ is the Coulomb potential:
--   $$V_{g,\alpha,0}(r) = -g^2\,\frac{1}{r}.$$
--
--   This is the article's observation that for a massless exchange particle $e^{-\alpha m r}=e^0=1$, so the Yukawa potential reduces to $V_{\mathrm{Coulomb}}(r)=-g^2\frac1r$.
--
--   **Formalization Note** The identity holds for every real $r$, including $r=0$ where both sides equal $0$ by Lean's division convention.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Relation to Coulomb potential': m = 0 ⇒ e^{-αmr} = e^0 = 1, so V_Yukawa simplifies to V_Coulomb(r) = -g² (1/r).

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawaPotential_massless_eq_coulomb (g α r : ℝ) :
    yukawaPotential g α 0 r = -g ^ 2 * (1 / r) := by sorry
end YukawaPotential
