-- Prove2me | Theorems.Thm_syracuse_descends_range_291829_295829
-- name    : syracuse_descends_range_291829_295829
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:32:54.153565+00:00
-- url     : https://prove2.me/theorems/63477525-7e3e-4d45-9009-7ee2cc0cd6ab
-- title:
--   Syracuse descent for odd numbers between 291829 and 295829
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $291829 \le m \le 295829$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a *descent* statement, not a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point.
--
--   Descent is exactly what is needed to exclude cycles. The minimum of a nontrivial cycle can never descend, so any $m$ satisfying the above is disqualified from being a cycle minimum. This is cheaper to certify than convergence, because each orbit need only be followed until its first drop below $291829$ — which is automatically below $m$ — rather than all the way to $1$.
--
--   Half the range is handled uniformly rather than by certificate: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ for $m > 1$, a single step. Only the residues $m \equiv 3 \pmod 4$ need explicit orbit data, here $5780$ step facts.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [291829, 295829], one stage of the ladder raising the cycle-minimum threshold from 99781 to 330750. Unlike the convergence certificates it supersedes, these stages are mutually independent. Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_291829_295829 (m : ℕ) (hlo : 291829 ≤ m) (hhi : m ≤ 295829) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
