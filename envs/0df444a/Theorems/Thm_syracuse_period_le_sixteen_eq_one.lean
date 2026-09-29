-- Prove2me | Theorems.Thm_syracuse_period_le_sixteen_eq_one
-- name    : syracuse_period_le_sixteen_eq_one
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-09T03:24:40.941324+00:00
-- url     : https://prove2.me/theorems/1c2f4dfb-bc6f-4c2c-911a-b9545c3723c4
-- title:
--   No nontrivial Syracuse cycle of period at most sixteen
-- statement:
--   Let $T$ denote the Syracuse map, sending $n$ to the odd part of $3n+1$. If $m$ is a positive integer with $T^a(m) = m$ for some $a$ with $1 \le a \le 16$, then $m = 1$.
--
--   Equivalently: every Syracuse cycle whose length is at most $16$ is the trivial cycle $\{1\}$. Note that no minimality is assumed of $a$ — it is any return time, not necessarily the least one.
--
--   This subsumes and extends the individually established exclusions for return times $1$ through $7$. The proof is uniform: for each of the sixteen periods one checks a single numerical margin inequality $103^a < 2^{K_a}\,34^a$, where $K_a$ is the least exponent with $3^a < 2^{K_a}$, and feeds it to the margin criterion. The value $34$ enters because no nontrivial Syracuse cycle contains a value at most $33$.
--
--   The bound $16$ is exactly where this method stops: the margin inequality holds for every $a \le 16$ and fails first at $a = 17$, where $2^{27}/3^{17} \approx 1.0393$ is smaller than $(103/34)^{17}/3^{17} \approx 1.181$.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; uniform strengthening of syracuse_fixed_point_eq_one ... syracuse_seven_cycle_eq_one via syracuse_cycle_eq_one_of_margin. Cf. J. C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 5.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_period_le_sixteen_eq_one (m a : ℕ) (hm : 0 < m) (ha : 0 < a) (hle : a ≤ 16)
    (hcyc : syracuseStep^[a] m = m) : m = 1 := by sorry
