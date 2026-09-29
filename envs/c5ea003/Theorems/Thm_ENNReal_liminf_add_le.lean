-- Prove2me | Theorems.Thm_ENNReal_liminf_add_le
-- name    : ENNReal.liminf_add_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T10:45:38.199989+00:00
-- url     : https://prove2.me/theorems/b20358f2-175c-447a-ba1a-fb9daf1d240a
-- title:
--   Lower limit of a sum is at most lower limit plus upper limit, on the extended nonnegative reals
-- statement:
--   For any nontrivial filter $l$ and functions $F,G:\iota\to[0,\infty]$,
--   $$\liminf_{l}\,(F+G)\ \le\ \liminf_{l}F+\limsup_{l}G .$$
--
--   **Role.** The companion of superadditivity: together the two say that $\liminf(F+G)$ is squeezed between $\liminf F+\liminf G$ and $\liminf F+\limsup G$, so that a sum of two quantities has a genuine limit as soon as one summand does. This is the shape of every argument in which an energy defined as a lower limit is compared with a sum of pieces: without it, an exact identity between approximate energies at each scale yields only an inequality in the wrong direction after passing to the limit. Mathlib proves the corresponding statement for functions valued in a topological ordered group (`liminf_add_le`), which excludes $[0,\infty]$.
--
--   **Proof.** By the approximation principle for $[0,\infty]$ it suffices, for each $\varepsilon>0$ with $\liminf F+\limsup G$ finite, to bound $\liminf(F+G)$ by $\liminf F+\limsup G+\varepsilon$. Finiteness makes $\limsup G$ finite, so $\limsup G<\limsup G+\varepsilon$, and hence $G<\limsup G+\varepsilon$ eventually. Monotonicity of the lower limit then bounds $\liminf(F+G)$ by $\liminf\bigl(F+(\limsup G+\varepsilon)\bigr)$, which is $\liminf F+\limsup G+\varepsilon$ because adding a constant commutes with the lower limit.
-- source:
--   Mathlib gap: `liminf_add_le` in Mathlib.Topology.Algebra.Order.LiminfLimsup requires a topological ordered group, which excludes the extended nonnegative reals.

import Mathlib

namespace ENNReal

theorem liminf_add_le {ι : Type*} (l : Filter ι) [l.NeBot] (F G : ι → ENNReal) :
    Filter.liminf (fun x => F x + G x) l
      ≤ Filter.liminf F l + Filter.limsup G l := by sorry

end ENNReal
