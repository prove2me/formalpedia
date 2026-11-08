-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_2887463
-- name    : syracuse_no_cycle_below_2887463
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:33:52.124022+00:00
-- url     : https://prove2.me/theorems/ef7628cb-d8e8-4cd0-a7f6-af252ae35745
-- title:
--   No nontrivial Syracuse cycle state below $2{,}887{,}463$
-- statement:
--   Let $T(n) = \operatorname{ordCompl}_2(3n + 1)$ denote the accelerated Syracuse map, sending $n$ to the odd part of $3n + 1$. If $m$ and $p$ are positive natural numbers ($m > 0$, $p > 0$) satisfying $m < 2{,}887{,}463$ and $T^p(m) = m$, then
--
--   $$m = 1.$$
--
--   The return period $p$ need not be minimal and the state $m$ need not be the minimum of its periodic orbit. This theorem upgrades the certified finite Syracuse cycle-state exclusion threshold from $2{,}786{,}502$ (`syracuse_no_cycle_below_2786502`) to $2{,}887{,}463$, exceeding the mechanical numerator quotient $2{,}855{,}819$ at $(p, K) = (6956, 11025)$.
-- source:
--   Finite extension of syracuse_no_cycle_below_2786502 (8b82562a-08bf-4b83-a7b3-36f0e888a07f, proved by user fizzyinc3, 0b3e45cf-260e-4cc3-a72e-1086b677e5d0, submission cbbe7edd-36de-4b3b-b13a-4dc55450f842) for Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67, combining syracuse_periodic_reaches_one (a46524f0-afd4-4232-b74a-8a95d7ab31a5), syracuse_descent_three_mod_four_2687463_to_2787459 (3c9b8324-db46-4b19-9927-96058a88cf51), and syracuse_descent_three_mod_four_2787463_to_2887459.

import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_no_cycle_below_2887463 (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hlt : m < 2887463) (hcyc : syracuseStep^[p] m = m) :
    m = 1 := by sorry
