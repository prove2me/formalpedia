-- Prove2me | Theorems.Thm_syracuse_period_le_twohundredfiftytwo_eq_one
-- name    : syracuse_period_le_twohundredfiftytwo_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:26:24.74224+00:00
-- url     : https://prove2.me/theorems/ccd61b51-0d5a-44f9-a86f-173422f5b992
-- title:
--   No nontrivial Syracuse cycle of period at most two hundred and fifty-two
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 252$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $252$ is the trivial cycle $\{1\}$. The return time $a$ need not be minimal.
--
--   The proof is uniform across the $252$ periods. For each $a$ one checks the single numerical inequality
--   $$38476^a \ <\ 2^{K_a}\cdot 12825^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion; the threshold $12825$ is available because no nontrivial cycle contains a value below $12825$. At $a = 252$ these compare integers of about $1060$ digits.
--
--   The least threshold covering every period up to $a$ grows without bound: it is $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305$, with the jumps landing on denominators of convergents of $\log_2 3$, where $2^{K_a}/3^a$ returns close to $1$. No single threshold serves every period, so this argument cannot settle the cycle question outright — but no finite period defeats it either. Only the certificate size, and hence the formalisation cost, grows without limit.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_12825. Strengthens syracuse_period_le_onehundredninetynine_eq_one (8d28c319-3f97-4b53-bf48-a1c95a2bd5d2). Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5; Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_twohundredfiftytwo_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 252) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
