-- Prove2me | Theorems.Thm_syracuse_descends_below_1166400
-- name    : syracuse_descends_below_1166400
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:22:35.392315+00:00
-- url     : https://prove2.me/theorems/bc30002f-646b-4259-b6bd-7acaea814b7a
-- title:
--   Every odd number above one and below 1166400 has a strictly smaller Syracuse iterate
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 < m < 1166400$, some iterate of $T$ falls strictly below $m$.
--
--   This is a descent statement, deliberately weaker than convergence, and exactly the strength cycle exclusion requires: the minimum of a nontrivial cycle can never descend.
--
--   Below $860564$ the result is inherited from the previous descent bound. Above it, the statement comes from a ladder of mutually independent range lemmas, each following orbits only until their first drop below that range's own lower bound. Half of every range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; assembled from syracuse_descends_below_860564 and 77 independent descent range lemmas covering [860564, 1166399].

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_below_1166400 (m : ℕ) (h1 : 1 < m) (hlt : m < 1166400) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
