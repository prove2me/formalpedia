-- Prove2me | Theorems.Thm_syracuse_period_le_twentythreehundred_eq_one
-- name    : syracuse_period_le_twentythreehundred_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T18:28:50.071359+00:00
-- url     : https://prove2.me/theorems/8f0d57f7-454f-4f9d-9831-6ca46ea43121
-- title:
--   No nontrivial Syracuse cycle of period at most 2300
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 2300$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $2300$ is the trivial cycle $\{1\}$; the return time need not be minimal.
--
--   The proof is uniform across the $2300$ periods: for each $a$ one checks the single numerical inequality
--   $$1749865^a \ <\ 2^{K_a}\cdot 583288^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion. The threshold $583288$ is available because no nontrivial cycle contains a value below it. At $a = 2300$ one has $K_a = 3646$ and the comparison is between integers of roughly $13000$ digits.
--
--   Period $2301$ is the first not covered. Writing $B(a)$ for the least threshold covering every period up to $a$, the sequence runs $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750, 583288$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970, 1635, 2300$, with jumps at denominators of convergents of $\log_2 3$. Since $B(a) \to \infty$, no single threshold covers every period, so a finite verification of this kind can never settle the cycle question; equally, no finite period defeats the method — only the certificate size grows without bound.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_583288. Strengthens syracuse_period_le_sixteenthirtyfive_eq_one (6e552b56-d48e-4701-ab43-2568630bfa8c). Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 5; Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_twentythreehundred_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 2300) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
