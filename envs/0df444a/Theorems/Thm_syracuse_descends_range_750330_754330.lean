-- Prove2me | Theorems.Thm_syracuse_descends_range_750330_754330
-- name    : syracuse_descends_range_750330_754330
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:50:35.462751+00:00
-- url     : https://prove2.me/theorems/6e5e4561-069a-4dd4-8d77-708998e2175e
-- title:
--   Syracuse descent for odd numbers between 750330 and 754330
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $750330 \le m \le 754330$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point. That is precisely the strength cycle exclusion needs, because the minimum of a nontrivial cycle can never descend.
--
--   Descent is also what keeps the certificate small. Each orbit is followed only until its first drop below $750330$ — automatically below $m$ — instead of all the way to $1$, and half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $5913$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $583288$ to $860564$. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [750330, 754330], one independent stage of the ladder raising the cycle-minimum threshold from 583288 to 860564. Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_750330_754330 (m : ℕ) (hlo : 750330 ≤ m) (hhi : m ≤ 754330) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
