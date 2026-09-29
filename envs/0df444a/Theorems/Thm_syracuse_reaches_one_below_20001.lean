-- Prove2me | Theorems.Thm_syracuse_reaches_one_below_20001
-- name    : syracuse_reaches_one_below_20001
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:43:09.568766+00:00
-- url     : https://prove2.me/theorems/1ff7dfa5-7da8-42ff-8742-62e93409c243
-- title:
--   Every odd number below 20001 reaches one under the Syracuse map
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 \le m \le 20000$ there is a $k \ge 0$ with $T^k(m) = 1$.
--
--   This is an intermediate step between the verified bounds $12824$ and $27113$, and it is stated separately for a practical reason: the platform limits a submitted proof to one megabyte of source, and the certificate reaching $27113$ in one piece exceeds that. Splitting the range lets each stage be checked on its own.
--
--   The stage is also much cheaper than a certificate built from scratch. Since every odd number below $12825$ is already known to reach $1$, an orbit starting in $[12825, 20000]$ only has to be followed until it first drops below $12825$; from there the earlier result takes over. That reduces the work to $9464$ orbit facts rather than the full closure down to $1$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; intermediate range lemma between syracuse_reaches_one_below_12825 (54949606-2480-4ab0-a440-8a89f7def9f2) and syracuse_reaches_one_below_27114 (db1399ea-58b1-4a28-88d6-e0895b5f8397), introduced to keep each submission within the one-megabyte source limit. Orbit data agrees with the standard 3x+1 tables, cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_reaches_one_below_20001 (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 20000) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by sorry
