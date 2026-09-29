-- Prove2me | Theorems.Thm_syracuse_descends_range_956588_960588
-- name    : syracuse_descends_range_956588_960588
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:06:18.462898+00:00
-- url     : https://prove2.me/theorems/307a0d9e-f8b7-4f23-b11e-2f83ad813271
-- title:
--   Syracuse descent for odd numbers between 956588 and 960588
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $956588 \le m \le 960588$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement rather than a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point. That is precisely the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Descent also keeps the certificate small. Each orbit is followed only until its first drop below $956588$ — automatically below $m$ — instead of all the way to $1$, and half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in a single step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $5939$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $860564$ to $1166400$. The stages are mutually independent — none imports another — so they may be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [956588, 960588], one independent stage of the ladder raising the cycle-minimum threshold from 860564 to 1166400. Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_956588_960588 (m : ℕ) (hlo : 956588 ≤ m) (hhi : m ≤ 960588) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
