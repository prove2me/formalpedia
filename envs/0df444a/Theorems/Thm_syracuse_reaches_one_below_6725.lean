-- Prove2me | Theorems.Thm_syracuse_reaches_one_below_6725
-- name    : syracuse_reaches_one_below_6725
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:02:13.177837+00:00
-- url     : https://prove2.me/theorems/45c3282c-ba70-4217-a69c-0b2bf4aaead2
-- title:
--   Every odd number below 6725 reaches one under the Syracuse map
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 \le m \le 6724$ there is a $k \ge 0$ with $T^k(m) = 1$.
--
--   This is a finite verification. The $3362$ odd starting values below $6725$ have orbits meeting $5258$ distinct odd numbers in total, the largest being $2717873$, and every one of those orbits terminates at $1$.
--
--   Its role is to supply the small-value input to the margin criterion for excluding Syracuse cycles: combined with the fact that a periodic point whose orbit reaches $1$ must equal $1$, it shows no nontrivial Syracuse cycle contains a value below $6725$, which in turn excludes every cycle of period at most $199$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; extension of syracuse_reaches_one_below_1193 (8771b7ae-8b1e-4838-bc0e-3a832f941d33) from bound 1192 to bound 6724. Orbit data agrees with the standard 3x+1 tables, cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_reaches_one_below_6725 (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 6724) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by sorry
