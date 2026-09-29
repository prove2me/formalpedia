-- Prove2me | Theorems.Thm_syracuse_descends_range_1651525_1653525
-- name    : syracuse_descends_range_1651525_1653525
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T23:34:02.060565+00:00
-- url     : https://prove2.me/theorems/92068d30-08a2-402d-bbdb-2aeef4e99074
-- title:
--   Syracuse descent for odd numbers between 1651525 and 1653525
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1651525 \le m \le 1653525$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement — nothing is claimed about where the orbit eventually goes, only that it dips below its starting point — and that is precisely the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Each orbit is followed only until its first drop below $1651525$, which is automatically below $m$, instead of all the way to $1$. Half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $2871$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $1505449$ to $1883432$. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [1651525, 1653525], one independent stage of the ladder raising the cycle-minimum threshold from 1505449 to 1883432.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_1651525_1653525 (m : ℕ) (hlo : 1651525 ≤ m) (hhi : m ≤ 1653525) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
