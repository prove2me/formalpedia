-- Prove2me | Theorems.Thm_syracuse_reaches_one_below_43118
-- name    : syracuse_reaches_one_below_43118
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:21:47.573876+00:00
-- url     : https://prove2.me/theorems/9657971c-7963-4db4-aae0-fd525b81bcc7
-- title:
--   Every odd number below 43118 reaches one under the Syracuse map
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 \le m \le 43117$ there is a $k \ge 0$ with $T^k(m) = 1$.
--
--   This is one stage of a ladder of verified bounds climbing towards $99780$, which is the small-value threshold at which the margin criterion excludes Syracuse cycles of every period up to $970$. The range is split into stages for two practical reasons: a submitted proof is limited to one megabyte of source and to five minutes of verification, and the whole range in one piece exceeds both by a wide margin.
--
--   Each stage is cheap because it stands on the previous one. Every odd number below $39117$ is already known to reach $1$, so an orbit starting in $[39117, 43117]$ need only be followed until it first drops below $39117$; the earlier result takes over from there. That costs $6767$ orbit facts rather than the full closure down to $1$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; stage [39117, 43117] of the reach ladder extending syracuse_reaches_one_below_27114 (db1399ea-58b1-4a28-88d6-e0895b5f8397) towards threshold 99781. Orbit data agrees with the standard 3x+1 tables, cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_reaches_one_below_43118 (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 43117) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by sorry
