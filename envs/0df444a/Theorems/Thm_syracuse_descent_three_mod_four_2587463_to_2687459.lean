-- Prove2me | Theorems.Thm_syracuse_descent_three_mod_four_2587463_to_2687459
-- name    : syracuse_descent_three_mod_four_2587463_to_2687459
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-28T11:43:25.944823+00:00
-- url     : https://prove2.me/theorems/058b76ab-b846-40b1-ab4b-927e46b2f13a
-- title:
--   Syracuse descent for $n \equiv 3 \pmod 4$, $2587463 \le n \le 2687459$
-- statement:
--   Let $S(n)$ denote the Syracuse (accelerated Collatz) map, sending $n$ to the odd part of $3n+1$. For every $j < 25000$, the number $n = 2587463 + 4j$ (so $n \equiv 3 \pmod 4$ and $2587463 \le n \le 2687459$) has a finite stopping time: some iterate $S^t(n)$ is strictly smaller than $n$. This is a finite verification band used in the proof that the Syracuse map has no nontrivial cycle with minimum below $2786502$.
-- source:
--   Finite stopping-time verification for the Collatz/Syracuse map (cf. Lagarias, The 3x+1 problem and its generalizations, Amer. Math. Monthly 92 (1985)); band of the reduction of syracuse_no_cycle_below_2786502 on Prove2Me.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_three_mod_four_2587463_to_2687459 (j : ℕ) (hj : j < 25000) :
    ∃ t : ℕ, syracuseStep^[t] (2587463 + 4 * j) < 2587463 + 4 * j := by sorry
