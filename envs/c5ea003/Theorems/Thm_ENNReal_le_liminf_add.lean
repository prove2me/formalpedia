-- Prove2me | Theorems.Thm_ENNReal_le_liminf_add
-- name    : ENNReal.le_liminf_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T10:04:49.176542+00:00
-- url     : https://prove2.me/theorems/36ca173e-c91c-471c-8083-5b402c5b066f
-- title:
--   The lower limit is superadditive on the extended nonnegative reals
-- statement:
--   For any filter $l$ on a type $\iota$ and any two functions $F,G:\iota\to[0,\infty]$,
--   $$\liminf_{l} F+\liminf_{l} G\ \le\ \liminf_{l}\,(F+G).$$
--
--   **Role.** Superadditivity of the lower limit is the elementary fact behind every "energy is at least the sum of its parts" statement. Mathlib proves it (`le_liminf_add`) for functions valued in a topological ordered *group*, which excludes $[0,\infty]$; but $[0,\infty]$ is exactly where lower semicontinuous quantities such as the Korevaar--Schoen energy — defined as a $\liminf$ of approximate energies — naturally live, and the group hypothesis is not needed: a complete lattice in which suprema distribute over addition suffices.
--
--   **Proof.** Write the lower limit in its lattice form $\liminf_l F=\bigvee_{s\in l}\bigwedge_{a\in s}F(a)$. Since $l$ contains the whole space, the index set is nonempty, so addition distributes over both suprema in $[0,\infty]$. It therefore suffices to bound, for $s,t\in l$,
--   $$\Bigl(\bigwedge_{a\in s}F(a)\Bigr)+\Bigl(\bigwedge_{a\in t}G(a)\Bigr)$$
--   by the lower limit of $F+G$. For every $a\in s\cap t$ the two infima are at most $F(a)$ and $G(a)$ respectively, so the sum is at most $F(a)+G(a)$, hence at most $\bigwedge_{a\in s\cap t}(F+G)(a)$; and $s\cap t\in l$, so this in turn is at most $\liminf_l (F+G)$.
-- source:
--   Mathlib gap: `le_liminf_add` in Mathlib.Topology.Algebra.Order.LiminfLimsup requires a topological ordered group, which excludes the extended nonnegative reals.

import Mathlib

namespace ENNReal

theorem le_liminf_add {ι : Type*} (l : Filter ι) (F G : ι → ENNReal) :
    Filter.liminf F l + Filter.liminf G l
      ≤ Filter.liminf (fun x => F x + G x) l := by sorry

end ENNReal
