-- Prove2me | Theorems.Thm_syracuse_descends_range_307833_311833
-- name    : syracuse_descends_range_307833_311833
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:33:05.011658+00:00
-- url     : https://prove2.me/theorems/58093cd7-f4ff-4bc0-bbe0-8c95b2aae336
-- title:
--   Syracuse descent for odd numbers between 307833 and 311833
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $307833 \le m \le 311833$, some iterate of $T$ falls strictly below $m$:
--   $$\exists\, t \ge 0 : \quad T^t(m) < m .$$
--
--   This is a *descent* statement, not a convergence statement: nothing is claimed about where the orbit eventually goes, only that it dips below its starting point.
--
--   Descent is exactly what is needed to exclude cycles. The minimum of a nontrivial cycle can never descend, so any $m$ satisfying the above is disqualified from being a cycle minimum. This is cheaper to certify than convergence, because each orbit need only be followed until its first drop below $307833$ — which is automatically below $m$ — rather than all the way to $1$.
--
--   Half the range is handled uniformly rather than by certificate: if $m \equiv 1 \pmod 4$ then $4 \mid 3m+1$, so $T(m) \le (3m+1)/4 < m$ for $m > 1$, a single step. Only the residues $m \equiv 3 \pmod 4$ need explicit orbit data, here $5856$ step facts.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; descent range [307833, 311833], one stage of the ladder raising the cycle-minimum threshold from 99781 to 330750. Unlike the convergence certificates it supersedes, these stages are mutually independent. Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descends_range_307833_311833 (m : ℕ) (hlo : 307833 ≤ m) (hhi : m ≤ 311833) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by sorry
