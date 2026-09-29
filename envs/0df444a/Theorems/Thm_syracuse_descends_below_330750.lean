-- Prove2me | Theorems.Thm_syracuse_descends_below_330750
-- name    : syracuse_descends_below_330750
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:22:32.519717+00:00
-- url     : https://prove2.me/theorems/898e645a-dec0-4554-abe0-fc83b48fa2f0
-- title:
--   Every odd number above one and below 330750 has a strictly smaller Syracuse iterate
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 < m < 330750$, some iterate of $T$ falls strictly below $m$.
--
--   This is a descent statement, weaker than convergence: nothing is asserted about where the orbit eventually goes. Its purpose is cycle exclusion, and for that it is exactly the right strength — the minimum of a nontrivial cycle can never descend, so every $m$ in this range is disqualified from being a cycle minimum.
--
--   Descent is also markedly cheaper to certify than convergence. Below $99781$ it is inherited from the existing convergence result, since an orbit reaching $1$ from $m > 1$ has certainly dropped below $m$. Above $99781$ it comes from a ladder of independent range lemmas, each of which follows orbits only until their first drop below that range's own lower bound. Half of each range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; assembled from syracuse_reaches_one_below_99781 (for m below 99781) and 58 independent descent range lemmas syracuse_descends_range_* covering [99781, 330749].

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_below_330750 (m : ℕ) (h1 : 1 < m) (hlt : m < 330750) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
