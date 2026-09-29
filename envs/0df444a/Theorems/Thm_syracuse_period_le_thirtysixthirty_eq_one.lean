-- Prove2me | Theorems.Thm_syracuse_period_le_thirtysixthirty_eq_one
-- name    : syracuse_period_le_thirtysixthirty_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T21:22:59.799437+00:00
-- url     : https://prove2.me/theorems/e758e753-b295-4172-8eaa-c0b7a11de73c
-- title:
--   No nontrivial Syracuse cycle of period at most 3630
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 3630$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $3630$ is the trivial cycle $\{1\}$; the return time need not be minimal.
--
--   The proof is uniform across the $3630$ periods: for each $a$ one checks the single numerical inequality
--   $$3499201^a \ <\ 2^{K_a}\cdot 1166400^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion. The threshold $1166400$ is available because no nontrivial cycle contains a value below it.
--
--   Period $3631$ is the first not covered. Writing $B(a)$ for the least threshold covering every period up to $a$, the sequence reads $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750, 583288, 860564, 1166400$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970, 1635, 2300, 2965, 3630$, the jumps landing on denominators of convergents of $\log_2 3$. Since $B(a) \to \infty$, no single threshold covers every period, so a finite verification of this kind can never settle the cycle question; equally, no finite period defeats the method — only the certificate size grows without bound.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_1166400. Strengthens syracuse_period_le_twentyninesixtyfive_eq_one. Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 5.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_thirtysixthirty_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 3630) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
