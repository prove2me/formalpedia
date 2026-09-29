-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_margin_at
-- name    : syracuse_cycle_eq_one_of_margin_at
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:40:29.638259+00:00
-- url     : https://prove2.me/theorems/756c30cf-ce03-4b10-afe8-8f76f671ae4f
-- title:
--   Margin criterion for Syracuse cycles at a general small-value threshold
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. This is the threshold-parametrised form of the margin criterion for excluding Syracuse cycles of a fixed period.
--
--   Fix a period $a \ge 1$ and a threshold $B \ge 1$, and suppose two things are known about $B$:
--
--   * **(small values)** every periodic point below $B$ is $1$; equivalently, no nontrivial cycle contains a value $< B$;
--   * **(margin)** every power of two exceeding $3^a$ also exceeds $\bigl((3B+1)/B\bigr)^a$, i.e. $(3B+1)^a < 2^K B^a$ whenever $3^a < 2^K$.
--
--   Then every $a$-periodic point of $T$ equals $1$.
--
--   The mechanism is a comparison of two inequalities holding around any cycle. Writing $m_0$ for the cycle minimum and $K = \sum_{i<a} v_2\bigl(3T^i(m_0)+1\bigr)$ for the total number of halvings, one has $3^a < 2^K$ and $2^K m_0^{\,a} \le (3m_0+1)^a$. A nontrivial cycle has $m_0 \ge B$ by the first assumption, which gives the linear estimate $B(3m_0+1) \le (3B+1)m_0$; raised to the $a$-th power this contradicts the margin assumption.
--
--   Separating the threshold $B$ from the argument is what makes the criterion usable: improving the verified range of small values immediately widens the set of periods that can be excluded, with no change to the proof. With $B = 34$ the margin condition holds exactly for $a \le 16$; with $B = 1193$ it holds exactly for $a \le 93$. It never holds for all $a$, since $2^K/3^a$ returns arbitrarily close to $1$ along the convergents of $\log_2 3$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; generalisation of syracuse_cycle_eq_one_of_margin (69029ed5-4448-4ffd-8171-205dbc67fa6c) with the small-value threshold as a parameter. Built from syracuse_cycle_pow_two_gt_pow_three (955877f3-88bd-4837-b1d9-2e4467430637) and syracuse_cycle_min_upper_bound (514577b7-9148-4a35-a0b2-80ac16b8b322). Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_cycle_eq_one_of_margin_at (a m B : ℕ) (ha : 0 < a) (hm : 0 < m) (hB : 0 < B)
    (hcyc : syracuseStep^[a] m = m)
    (hsmall : ∀ z b : ℕ, 0 < z → 0 < b → z < B → syracuseStep^[b] z = z → z = 1)
    (hbd : ∀ K : ℕ, 3 ^ a < 2 ^ K → (3 * B + 1) ^ a < 2 ^ K * B ^ a) :
    m = 1 := by sorry
