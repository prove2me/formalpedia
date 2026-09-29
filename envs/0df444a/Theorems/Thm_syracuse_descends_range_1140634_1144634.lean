-- Prove2me | Theorems.Thm_syracuse_descends_range_1140634_1144634
-- name    : syracuse_descends_range_1140634_1144634
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:07:32.174981+00:00
-- url     : https://prove2.me/theorems/728776d3-8c26-422d-b553-1f2a479c95d9
-- title:
--   Syracuse descent for odd numbers between 1140634 and 1144634
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1140634 \le m \le 1144634$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point. That is precisely the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Descent also keeps the certificate small. Each orbit is followed only until its first drop below $1140634$ — automatically below $m$ — instead of all the way to $1$, and half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $6082$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $860564$ to $1166400$. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [1140634, 1144634], one independent stage of the ladder raising the cycle-minimum threshold from 860564 to 1166400. Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_1140634_1144634 (m : ℕ) (hlo : 1140634 ≤ m) (hhi : m ≤ 1144634) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
