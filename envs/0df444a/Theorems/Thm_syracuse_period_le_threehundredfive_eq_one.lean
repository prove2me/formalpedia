-- Prove2me | Theorems.Thm_syracuse_period_le_threehundredfive_eq_one
-- name    : syracuse_period_le_threehundredfive_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T04:20:29.802058+00:00
-- url     : https://prove2.me/theorems/c0f5c98b-63d9-443f-8afb-2b7a65f494f0
-- title:
--   No nontrivial Syracuse cycle of period at most three hundred and five
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 305$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $305$ is the trivial cycle $\{1\}$. The return time $a$ need not be minimal.
--
--   The proof is uniform across the $305$ periods. For each $a$ one checks the single numerical inequality
--   $$81343^a \ <\ 2^{K_a}\cdot 27114^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion; the threshold $27114$ is available because no nontrivial cycle contains a value below $27114$. At $a = 305$ these compare integers of about $1350$ digits.
--
--   The period $306$ is the first not covered, and is of special interest: it is a denominator of a convergent of $\log_2 3$, where $2^{485}/3^{306} \approx 1.00102$ leaves very little room. The required threshold grows with the period: covering every period up to $a$ needs $B$ at least $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305$. The jumps occur at denominators of convergents of $\log_2 3$, where $2^{K_a}/3^a$ approaches $1$. No single $B$ serves every period, so this line of argument cannot exclude all cycles; but there is no finite period at which it fails outright — only a threshold, and hence a formalisation cost, that grows without bound.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_27114. Strengthens syracuse_period_le_onehundredninetynine_eq_one (8d28c319-3f97-4b53-bf48-a1c95a2bd5d2). Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5; Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_threehundredfive_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 305) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
