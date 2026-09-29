-- Prove2me | Theorems.Thm_syracuse_descends_range_1407523_1409523
-- name    : syracuse_descends_range_1407523_1409523
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:49:56.428346+00:00
-- url     : https://prove2.me/theorems/8aad0bce-348d-475d-a01a-095179e53ec6
-- title:
--   Syracuse descent for odd numbers between 1407523 and 1409523
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1407523 \le m \le 1409523$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement — nothing is claimed about where the orbit eventually goes, only that it dips below its starting point — and that is precisely the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Each orbit is followed only until its first drop below $1407523$, which is automatically below $m$, instead of all the way to $1$. Half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $3044$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $1166400$ to $1505449$. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [1407523, 1409523], one independent stage of the ladder raising the cycle-minimum threshold from 1166400 to 1505449.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_1407523_1409523 (m : ℕ) (hlo : 1407523 ≤ m) (hhi : m ≤ 1409523) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
