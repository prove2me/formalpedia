-- Prove2me | Theorems.Thm_syracuse_period_le_ninetythree_eq_one
-- name    : syracuse_period_le_ninetythree_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:40:34.472955+00:00
-- url     : https://prove2.me/theorems/3794ed87-5e54-4843-a40b-28fa6724c62f
-- title:
--   No nontrivial Syracuse cycle of period at most ninety-three
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 93$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $93$ is the trivial cycle $\{1\}$. The return time $a$ need not be minimal.
--
--   The proof is uniform across the ninety-three periods. For each $a$ one checks the single numerical inequality
--   $$3580^a \ <\ 2^{K_a}\cdot 1193^a,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion; the threshold $1193$ is available because no nontrivial cycle contains a value below $1193$.
--
--   The bound $93$ is exactly where this method stops: the inequality holds for every $a \le 93$ and fails first at $a = 94$. Raising the verified small-value range would move the bound further — but never to all periods, since $2^{K_a}/3^a$ comes arbitrarily close to $1$ along the convergents of $\log_2 3$, most sharply at $a = 306$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at and syracuse_no_cycle_below_1193. Strengthens syracuse_period_le_sixteen_eq_one (1c2f4dfb-bc6f-4c2c-911a-b9545c3723c4). Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5; Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_ninetythree_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a) (hle : a ≤ 93)
    (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
