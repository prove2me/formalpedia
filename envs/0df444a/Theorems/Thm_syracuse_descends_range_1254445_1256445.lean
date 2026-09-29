-- Prove2me | Theorems.Thm_syracuse_descends_range_1254445_1256445
-- name    : syracuse_descends_range_1254445_1256445
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:47:52.587233+00:00
-- url     : https://prove2.me/theorems/9f50878b-8a4a-4d19-854a-ac5b0266b661
-- title:
--   Syracuse descent for odd numbers between 1254445 and 1256445
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1254445 \le m \le 1256445$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement — nothing is claimed about where the orbit eventually goes, only that it dips below its starting point — and that is precisely the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Each orbit is followed only until its first drop below $1254445$, which is automatically below $m$, instead of all the way to $1$. Half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $2929$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $1166400$ to $1505449$. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [1254445, 1256445], one independent stage of the ladder raising the cycle-minimum threshold from 1166400 to 1505449.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_1254445_1256445 (m : ℕ) (hlo : 1254445 ≤ m) (hhi : m ≤ 1256445) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
