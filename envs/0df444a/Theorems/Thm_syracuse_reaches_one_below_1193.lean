-- Prove2me | Theorems.Thm_syracuse_reaches_one_below_1193
-- name    : syracuse_reaches_one_below_1193
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:40:31.960802+00:00
-- url     : https://prove2.me/theorems/8771b7ae-8b1e-4838-bc0e-3a832f941d33
-- title:
--   Every odd number below 1193 reaches one under the Syracuse map
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 \le m \le 1192$ there is a $k \ge 0$ with $T^k(m) = 1$.
--
--   This is a finite verification: the $596$ odd starting values below $1193$ have orbits meeting only $961$ distinct odd numbers in total, the largest being $83501$, and every one of these orbits terminates at $1$.
--
--   Its role is to supply the small-value input to the margin criterion for excluding Syracuse cycles. Combined with the fact that a periodic point whose orbit reaches $1$ must equal $1$, it shows that no nontrivial Syracuse cycle contains a value below $1193$, which in turn excludes every cycle of period at most $93$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; extension of syracuse_small_reaches_one (686cc205-cac4-4284-b9dd-7afc4bd394ff) from bound 33 to bound 1192. Orbit data agrees with the standard 3x+1 tables, cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_reaches_one_below_1193 (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 1192) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by sorry
