-- Prove2me | Theorems.Thm_syracuse_period_le_ninehundredseventy_eq_one
-- name    : syracuse_period_le_ninehundredseventy_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T05:32:13.322851+00:00
-- url     : https://prove2.me/theorems/e3051e5b-8f44-4f00-8e6c-0286199106f2
-- title:
--   No nontrivial Syracuse cycle of period at most nine hundred and seventy
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 970$, then $m = 1$.
--
--   Equivalently, every Syracuse cycle of length at most $970$ is the trivial cycle $\{1\}$. The return time $a$ need not be minimal.
--
--   The proof is uniform across the $970$ periods. For each $a$ one checks the single numerical inequality
--   $$299344^a \ <\ 2^{K_a}\cdot 99781^a ,$$
--   where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion; the threshold $99781$ is available because no nontrivial cycle contains a value below $99781$. At $a = 970$ these compare integers of roughly $4900$ digits.
--
--   Period $971$ is the first not covered, and needs the threshold raised to $330750$. The least threshold $B(a)$ covering every period up to $a$ runs $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970$, with the jumps landing on denominators of convergents of $\log_2 3$, where $2^{K_a}/3^a$ returns close to $1$. Since $B(a) \to \infty$, no single threshold serves every period, and this argument cannot settle the cycle question outright — but no finite period defeats it either. Only the certificate size, and hence the formalisation cost, grows without limit.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; from syracuse_cycle_eq_one_of_margin_at (756c30cf-ce03-4b10-afe8-8f76f671ae4f) and syracuse_no_cycle_below_99781. Strengthens syracuse_period_le_threehundredfive_eq_one (c0f5c98b-63d9-443f-8afb-2b7a65f494f0). Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5; Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_ninehundredseventy_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a)
    (hle : a ≤ 970) (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
