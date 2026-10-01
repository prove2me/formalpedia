-- Prove2me | Theorems.Thm_syracuse_descends_range_2281435_2283435
-- name    : syracuse_descends_range_2281435_2283435
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-23T16:44:59.465558+00:00
-- url     : https://prove2.me/theorems/b635680e-a40e-42c8-8445-467c4f8d278f
-- title:
--   Syracuse descent range [2281435, 2283435]
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $L \le m \le H$ ($2281435 \le m \le 2283435$), some iterate of $T$ falls strictly below $m$:
--
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement — nothing is claimed about where the orbit eventually goes, only that it dips below its starting point — and that is precisely the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Each orbit is followed only until its first drop below 2281435, which is automatically below $m$, instead of all the way to $1$. Half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here 2845 step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $1883432$ to $2310000$ — the range needed to close the period-$4961$ cycle-exclusion margin. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [2281435, 2283435], one independent stage of the ladder raising the cycle-minimum threshold from 1883432 to 2310000.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_2281435_2283435 (m : ℕ) (hlo : 2281435 ≤ m) (hhi : m ≤ 2283435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
