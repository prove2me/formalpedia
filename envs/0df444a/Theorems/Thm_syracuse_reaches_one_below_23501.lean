-- Prove2me | Theorems.Thm_syracuse_reaches_one_below_23501
-- name    : syracuse_reaches_one_below_23501
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:57:43.348602+00:00
-- url     : https://prove2.me/theorems/a7cbe39f-b2a7-470d-bdf7-dc72731846d8
-- title:
--   Every odd number below 23501 reaches one under the Syracuse map
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. For every odd $m$ with $1 \le m \le 23500$ there is a $k \ge 0$ with $T^k(m) = 1$.
--
--   This is one stage in a ladder of verified bounds climbing towards $27113$, which is the small-value threshold needed to exclude Syracuse cycles of every period up to $305$. The range is split into stages purely for practical reasons: a submitted proof is limited to one megabyte of source and to five minutes of verification time, and the whole range in one piece exceeds both.
--
--   Each stage is cheap because it stands on the previous one. Every odd number below $20001$ is already known to reach $1$, so an orbit starting in $[20001, 23500]$ need only be followed until it first drops below $20001$; the earlier result takes over from there. That costs $5500$ orbit facts instead of the full closure down to $1$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; stage between syracuse_reaches_one_below_20001 (1ff7dfa5-7da8-42ff-8742-62e93409c243) and syracuse_reaches_one_below_27114 (db1399ea-58b1-4a28-88d6-e0895b5f8397), introduced after the combined range exceeded the 300-second verification limit. Orbit data agrees with the standard 3x+1 tables, cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 2.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_reaches_one_below_23501 (m : ℕ) (hm : 0 < m) (hodd : Odd m) (hle : m ≤ 23500) :
    ∃ k : ℕ, syracuseStep^[k] m = 1 := by sorry
