-- Prove2me | Theorems.Thm_syracuse_descends_range_539803_542803
-- name    : syracuse_descends_range_539803_542803
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:35:46.462677+00:00
-- url     : https://prove2.me/theorems/f80c6af3-3db0-4af0-bd50-eca7e2012cce
-- title:
--   Syracuse descent for odd numbers between 539803 and 542803
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $539803 \le m \le 542803$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a descent statement, not a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point. That is exactly the strength cycle exclusion needs, since the minimum of a nontrivial cycle can never descend.
--
--   Descent is also what keeps the certificate small. Each orbit is followed only until its first drop below $539803$ — automatically below $m$ — rather than all the way to $1$, and half the range needs no orbit data at all: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ in one step. Only the residues $m \equiv 3 \pmod 4$ require explicit data, here $4655$ step facts.
--
--   This lemma is one stage of a ladder raising the cycle-minimum threshold from $330750$ to $583288$. The stages are mutually independent: none imports another, so they can be checked in any order or concurrently.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [539803, 542803], one independent stage of the ladder raising the cycle-minimum threshold from 330750 to 583288. Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_539803_542803 (m : ℕ) (hlo : 539803 ≤ m) (hhi : m ≤ 542803) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
