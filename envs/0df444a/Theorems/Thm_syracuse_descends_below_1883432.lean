-- Prove2me | Theorems.Thm_syracuse_descends_below_1883432
-- name    : syracuse_descends_below_1883432
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:21:49.564532+00:00
-- url     : https://prove2.me/theorems/8c47f928-3c80-4537-ad4a-bbc204bc04d9
-- title:
--   Every odd number above one and below 1883432 has a strictly smaller Syracuse iterate
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 < m < 1883432$, some iterate of $T$ falls strictly below $m$.
--
--   This is a descent statement, deliberately weaker than convergence, and exactly the strength cycle exclusion requires: the minimum of a nontrivial cycle can never descend.
--
--   Below $1505449$ the result is inherited from the previous descent bound. Above it, the statement comes from a ladder of $195$ mutually independent range lemmas, each following orbits only until their first drop below that range's own lower bound. Half of every range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; assembled from syracuse_descends_below_1505449 and 195 independent descent range lemmas covering [1505449, 1883431].

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_below_1883432 (m : ℕ) (h1 : 1 < m) (hlt : m < 1883432) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
