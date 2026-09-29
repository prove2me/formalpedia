-- Prove2me | Theorems.Thm_syracuse_period_le_twentyninesixtyfive_eq_one
-- name    : syracuse_period_le_twentyninesixtyfive_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:42:16.199654+00:00
-- url     : https://prove2.me/theorems/73232582-1113-44b0-a1e0-a1012bdf1683
-- title:
--   No nontrivial Syracuse cycle of period at most 2965
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 2965$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $2965$ is the trivial cycle $\{1\}$; the return time need not be minimal.
--
--   The proof is uniform across the $2965$ periods: for each $a$ one checks the single numerical inequality
--   $$2581693^a \ <\ 2^{K_a}\cdot 860564^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion. The threshold $860564$ is available because no nontrivial cycle contains a value below it.
--
--   Period $2966$ is the first not covered. Writing $B(a)$ for the least threshold covering every period up to $a$, the sequence now reads $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750, 583288, 860564$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970, 1635, 2300, 2965$, the jumps landing on denominators of convergents of $\log_2 3$. Since $B(a) \to \infty$, no single threshold covers every period, so a finite verification of this kind can never settle the cycle question; equally, no finite period defeats the method — only the certificate size grows without bound.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_860564. Strengthens syracuse_period_le_twentythreehundred_eq_one. Cf. J. C. Lagarias, Amer. Math. Monthly 92 (1985), Section 5.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_twentyninesixtyfive_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 2965) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
