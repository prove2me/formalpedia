-- Prove2me | Theorems.Thm_YukawaPotential_yukawaPotential_neg_and_strictMonoOn
-- name    : YukawaPotential.yukawaPotential_neg_and_strictMonoOn
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T12:25:26.879984+00:00
-- url     : https://prove2.me/theorems/d7a33820-0d9b-43c9-99df-5c680cf492de
-- title:
--   Yukawa potential is negative and strictly increasing on $(0,\infty)$
-- statement:
--   Let $g\neq 0$, $\alpha>0$ and $m\ge 0$, and let $V(r)=-g^2 e^{-\alpha m r}/r$ be the Yukawa potential. Then
--
--   1. $V(r)<0$ for every $r>0$, and
--   2. $V$ is strictly increasing on $(0,\infty)$:
--   $$0<r_1<r_2 \implies V(r_1)<V(r_2).$$
--
--   This is the article's statement that "the potential is monotonically increasing in $r$ and it is negative, implying the force is attractive".
--
--   **Formalization Note** The hypothesis $g\neq0$ excludes the identically zero potential; $\alpha>0$ and $m\ge0$ are the physical conventions on the scaling constant and the mass.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, introduction (first paragraph): 'The potential is monotonically increasing in r and it is negative'.

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem yukawaPotential_neg_and_strictMonoOn (g α m : ℝ) (hg : g ≠ 0) (hα : 0 < α) (hm : 0 ≤ m) :
    (∀ r : ℝ, 0 < r → yukawaPotential g α m r < 0) ∧
      StrictMonoOn (yukawaPotential g α m) (Set.Ioi 0) := by sorry
end YukawaPotential
