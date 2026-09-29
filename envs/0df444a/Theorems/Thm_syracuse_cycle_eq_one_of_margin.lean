-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_margin
-- name    : syracuse_cycle_eq_one_of_margin
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:24:43.749455+00:00
-- url     : https://prove2.me/theorems/69029ed5-4448-4ffd-8171-205dbc67fa6c
-- title:
--   Margin criterion excluding nontrivial Syracuse cycles of a fixed period
-- statement:
--   Let $T$ denote the Syracuse map, sending $n$ to the odd part of $3n+1$. Fix a period $a \ge 1$ and suppose $T^a(m) = m$ for some $m > 0$.
--
--   Let $m_0$ be the least value on the cycle and let
--   $$K = \sum_{i<a} v_2\bigl(3\,T^i(m_0)+1\bigr)$$
--   be the total number of halvings performed around the cycle. Two known inequalities govern the cycle: $3^a < 2^K$, and $2^K m_0^{\,a} \le (3m_0+1)^a$.
--
--   It is also known that no nontrivial Syracuse cycle contains a value at most $33$. So on a nontrivial cycle $m_0 \ge 34$, which gives the linear estimate $34(3m_0+1) \le 103\,m_0$; raising it to the $a$-th power and combining with the two inequalities above forces
--   $$103^a \ \ge\ 2^K \cdot 34^a .$$
--
--   This theorem is the contrapositive. It says that whenever the period $a$ has *positive margin* — meaning that every power of two which already exceeds $3^a$ also exceeds $(103/34)^a$, which is the hypothesis $\mathtt{hbd}$ — no nontrivial cycle of period $a$ can exist, so $m=1$.
--
--   The hypothesis is a purely numerical condition on $a$ alone, checkable by a single comparison of integers, since it suffices to verify it for the least exponent $K$ with $3^a < 2^K$. It therefore turns cycle exclusion at each fixed period into arithmetic, with no case analysis over the cycle. The criterion holds for every $a \le 16$ and first fails at $a = 17$; it is not a proof that all Collatz cycles are trivial.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; derived from syracuse_cycle_pow_two_gt_pow_three (955877f3-88bd-4837-b1d9-2e4467430637), syracuse_cycle_min_upper_bound (514577b7-9148-4a35-a0b2-80ac16b8b322) and syracuse_no_small_cycle (f2ae2367-c0d1-487d-b130-29f6669676db). Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5 (cycle inequalities).

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_cycle_eq_one_of_margin (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    (hcyc : syracuseStep^[a] m = m)
    (hbd : ∀ K : ℕ, 3 ^ a < 2 ^ K → 103 ^ a < 2 ^ K * 34 ^ a) :
    m = 1 := by sorry
