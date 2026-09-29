-- Prove2me | Theorems.Thm_syracuse_period_le_onehundredninetynine_eq_one
-- name    : syracuse_period_le_onehundredninetynine_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:02:19.060839+00:00
-- url     : https://prove2.me/theorems/8d28c319-3f97-4b53-bf48-a1c95a2bd5d2
-- title:
--   No nontrivial Syracuse cycle of period at most one hundred and ninety-nine
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 199$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $199$ is the trivial cycle $\{1\}$. The return time $a$ need not be minimal.
--
--   The proof is uniform across the $199$ periods. For each $a$ one checks the single numerical inequality
--   $$20176^a \ <\ 2^{K_a}\cdot 6725^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion; the threshold $6725$ is available because no nontrivial cycle contains a value below $6725$. At $a = 199$ these are comparisons of $857$-digit integers.
--
--   The bound $199$ is exactly where this threshold stops: the inequality holds for every $a \le 199$ and fails first at $a = 200$. Enlarging the verified small-value range moves the boundary further, but never to all periods — $2^{K_a}/3^a$ comes arbitrarily close to $1$ along the convergents of $\log_2 3$, and at $a = 306$ no threshold whatsoever suffices.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_6725. Strengthens syracuse_period_le_ninetythree_eq_one (3794ed87-5e54-4843-a40b-28fa6724c62f). Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5; Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_onehundredninetynine_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 199) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
