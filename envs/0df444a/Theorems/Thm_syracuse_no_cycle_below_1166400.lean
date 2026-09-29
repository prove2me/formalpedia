-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_1166400
-- name    : syracuse_no_cycle_below_1166400
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:22:33.742513+00:00
-- url     : https://prove2.me/theorems/5e06c428-2deb-4aa9-93d3-820aca97e1e9
-- title:
--   No nontrivial Syracuse cycle contains a value below 1166400
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $z$ is a positive integer with $z \le 1166399$ and $T^a(z) = z$ for some $a \ge 1$, then $z = 1$. The return time is arbitrary; no minimality is assumed.
--
--   Pass to the least value $w$ on the orbit of $z$. Then $w \le z < 1166400$, and $w$ is odd and positive because it is a value of $T$. Were $w$ greater than $1$ it would admit a strictly smaller iterate by the descent result for this range — impossible, since $w$ is the orbit minimum. Hence $w = 1$, the orbit of $z$ reaches $1$, and a periodic point whose orbit reaches $1$ is itself $1$.
--
--   Only descent is used, never convergence; that is what keeps the threshold cheap to raise.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_descends_below_1166400 and syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_no_cycle_below_1166400 (z a : ℕ) (hz : 0 < z) (ha : 0 < a) (hle : z ≤ 1166399)
    (hcyc : syracuseStep^[a] z = z) : z = 1 := by sorry
