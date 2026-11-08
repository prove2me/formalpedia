-- Prove2me | Theorems.Thm_syracuse_descent_three_mod_four_2787463_to_2887459
-- name    : syracuse_descent_three_mod_four_2787463_to_2887459
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:52.396836+00:00
-- url     : https://prove2.me/theorems/571c1725-2696-4cba-b48f-2c5b0ad14df1
-- title:
--   Syracuse descent for $n \equiv 3 \pmod 4$, $2787463 \le n \le 2887459$
-- statement:
--   Let $T(n) = \operatorname{ordCompl}_2(3n + 1)$ denote the accelerated Syracuse map, sending each natural number $n$ to the odd part of $3n + 1$. For every natural number $j < 25{,}000$, the odd integer $n = 2{,}787{,}463 + 4j$ (satisfying $n \equiv 3 \pmod{4}$ and $2{,}787{,}463 \le n \le 2{,}887{,}459$) has a finite stopping time under iteration of $T$: there exists a step count $t \in \mathbb{N}$ such that
--
--   $$T^t(2{,}787{,}463 + 4j) < 2{,}787{,}463 + 4j.$$
--
--   This theorem provides the next $100{,}000$-wide finite verification band along the residue class $n \equiv 3 \pmod{4}$ beyond `syracuse_descent_three_mod_four_2687463_to_2787459`, extending the certified Syracuse cycle-exclusion baseline from $2{,}786{,}502$ to $2{,}887{,}463$.
-- source:
--   Collatz cycle-exclusion frontier extension (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), extending the finite verification band syracuse_descent_three_mod_four_2687463_to_2787459 (3c9b8324-db46-4b19-9927-96058a88cf51) by user fizzyinc3 (0b3e45cf-260e-4cc3-a72e-1086b677e5d0); cf. Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_descent_three_mod_four_2787463_to_2887459 (j : ℕ) (hj : j < 25000) :
    ∃ t : ℕ, syracuseStep^[t] (2787463 + 4 * j) < 2787463 + 4 * j := by sorry
