-- Prove2me | Theorems.Thm_syracuse_period_le_sixteenthirtyfive_eq_one
-- name    : syracuse_period_le_sixteenthirtyfive_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:22:30.89737+00:00
-- url     : https://prove2.me/theorems/6e552b56-d48e-4701-ab43-2568630bfa8c
-- title:
--   No nontrivial Syracuse cycle of period at most 1635
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 1635$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $1635$ is the trivial cycle $\{1\}$. The return time need not be minimal.
--
--   The proof is uniform across the $1635$ periods: for each $a$ one checks the single numerical inequality
--   $$992251^a \ <\ 2^{K_a}\cdot 330750^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion. The threshold $330750$ is available because no nontrivial cycle contains a value below it. At $a = 1635$ one has $K_a = 2592$ and the comparison is between integers of about $9000$ digits.
--
--   Period $1636$ is the first not covered. Writing $B(a)$ for the least threshold covering every period up to $a$, the sequence runs $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970, 1635$, with jumps at denominators of convergents of $\log_2 3$. Since $B(a) \to \infty$, no single threshold covers all periods, so this argument cannot settle the cycle question — but no finite period defeats it either; only the certificate size grows without bound.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_330750. Strengthens syracuse_period_le_ninehundredseventy_eq_one (e3051e5b-8f44-4f00-8e6c-0286199106f2). Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 5; Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_sixteenthirtyfive_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 1635) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
