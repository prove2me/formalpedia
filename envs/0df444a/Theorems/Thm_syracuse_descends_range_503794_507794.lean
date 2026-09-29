-- Prove2me | Theorems.Thm_syracuse_descends_range_503794_507794
-- name    : syracuse_descends_range_503794_507794
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:35:33.813915+00:00
-- url     : https://prove2.me/theorems/ebb08b3b-43e1-4d22-9d1c-5b1452db43d3
-- title:
--   Syracuse descent for odd numbers between 503794 and 507794
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $503794 \le m \le 507794$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement, not a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point. That is exactly the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Descent is also what keeps the certificate small. Each orbit is followed only until its first drop below $503794$ — automatically below $m$ — rather than all the way to $1$, and half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in one step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $5881$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $330750$ to $583288$. The stages are mutually independent: none imports another, so they can be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [503794, 507794], one independent stage of the ladder raising the cycle-minimum threshold from 330750 to 583288. Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_503794_507794 (m : ℕ) (hlo : 503794 ≤ m) (hhi : m ≤ 507794) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
