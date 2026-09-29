-- Prove2me | Theorems.Thm_syracuse_descends_range_1132632_1136632
-- name    : syracuse_descends_range_1132632_1136632
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:07:27.659138+00:00
-- url     : https://prove2.me/theorems/def61485-35cb-495e-80d2-369a40c47243
-- title:
--   Syracuse descent for odd numbers between 1132632 and 1136632
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1132632 \le m \le 1136632$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point. That is precisely the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Descent also keeps the certificate small. Each orbit is followed only until its first drop below $1132632$ — automatically below $m$ — instead of all the way to $1$, and half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $5763$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $860564$ to $1166400$. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [1132632, 1136632], one independent stage of the ladder raising the cycle-minimum threshold from 860564 to 1166400. Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_1132632_1136632 (m : ℕ) (hlo : 1132632 ≤ m) (hhi : m ≤ 1136632) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
