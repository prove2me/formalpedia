-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_330750
-- name    : syracuse_no_cycle_below_330750
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:22:31.449511+00:00
-- url     : https://prove2.me/theorems/96774dff-bb66-4012-ba8c-ad6a91c837cb
-- title:
--   No nontrivial Syracuse cycle contains a value below 330750
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 330749$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$. The return time is arbitrary; no minimality is assumed.
--
--   The argument is the natural one for cycles. Passing to the least value $w$ on the orbit of $z$, one has $w \le z < 330750$, and $w$ is odd and positive because it is a value of $T$. If $w$ were greater than $1$ it would admit a strictly smaller iterate, by the descent result for this range — but $w$ is the orbit minimum, so no iterate of $w$ can lie below it. Hence $w = 1$, the orbit of $z$ reaches $1$, and a periodic point whose orbit reaches $1$ is itself $1$.
--
--   Note that only *descent* is needed, never convergence. That is what makes the threshold cheap to raise.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_descends_below_330750 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5). Supersedes syracuse_no_cycle_below_99781 (bb9842e2-a1a4-46c0-be27-ea9e7d8a90a5).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_330750 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 330749)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry
