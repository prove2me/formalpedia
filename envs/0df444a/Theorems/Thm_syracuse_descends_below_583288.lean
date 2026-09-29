-- Prove2me | Theorems.Thm_syracuse_descends_below_583288
-- name    : syracuse_descends_below_583288
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:28:46.394409+00:00
-- url     : https://prove2.me/theorems/7ad5add7-059c-4510-987a-f0f22fb30832
-- title:
--   Every odd number above one and below 583288 has a strictly smaller Syracuse iterate
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 < m < 583288$, some iterate of $T$ falls strictly below $m$.
--
--   This is a descent statement, deliberately weaker than convergence: nothing is asserted about where the orbit eventually goes. It is nonetheless exactly the strength cycle exclusion requires, since the minimum of a nontrivial cycle can never descend.
--
--   Below $330750$ the result is inherited from the previous descent bound. Above it, the statement comes from a ladder of $65$ mutually independent range lemmas, each following orbits only until their first drop below that range's own lower bound. Half of every range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; assembled from syracuse_descends_below_330750 and 65 independent descent range lemmas syracuse_descends_range_* covering [330750, 583287].

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_below_583288 (m : ℕ) (h1 : 1 < m) (hlt : m < 583288) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
