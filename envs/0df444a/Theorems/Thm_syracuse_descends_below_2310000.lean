-- Prove2me | Theorems.Thm_syracuse_descends_below_2310000
-- name    : syracuse_descends_below_2310000
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-23T18:27:42.791501+00:00
-- url     : https://prove2.me/theorems/aca87302-202e-4b56-936b-033a5d8116d2
-- title:
--   Syracuse descent below 2310000
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 < m < 2310000$, some iterate of $T$ falls strictly below $m$.
--
--   This is a descent statement, deliberately weaker than convergence, and exactly the strength cycle exclusion requires: the minimum of a nontrivial cycle can never descend.
--
--   Below $1883432$ the result is inherited from the previous descent bound. Above it, the statement comes from a ladder of $214$ mutually independent range lemmas, each following orbits only until their first drop below that range's own lower bound. Half of every range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step.
--
--   The threshold $2310000$ is chosen so that the cycle-margin criterion $syracuse\_cycle\_eq\_one\_of\_margin\_at$ closes the period-$4961$ cycle-exclusion gap: with $a = 4961$, $b = \lfloor a \log_2 3 \rfloor = 7862$, the margin inequality $(3B+1)^a < 2^{b+1} B^a$ first holds at $B \ge 2307463$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; assembled from syracuse_descends_below_1883432 and 214 independent descent range lemmas covering [1883432, 2309999].

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_below_2310000 (m : ℕ) (h1 : 1 < m) (hlt : m < 2310000) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
