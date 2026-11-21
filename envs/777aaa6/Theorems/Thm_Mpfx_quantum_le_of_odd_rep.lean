-- Prove2me | Theorems.Thm_Mpfx_quantum_le_of_odd_rep
-- name    : Mpfx.quantum_le_of_odd_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:57.24889+00:00
-- url     : https://prove2.me/theorems/9d541f8a-2fea-4c9f-b17b-cc7646e1bb1e
-- title:
--   Mpfx: quantum le of odd rep
-- statement:
--   An odd-significand representation cannot sit below the quantum: if
--   `x = c·2^q` with `c` odd and `x` has quantum at least `e`, then `e ≤ q`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L578-L589
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L578-L589

import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Utils
import Mathlib.Tactic
import Definitions.Def_Mpfx_Dyadic
set_option autoImplicit true
open Mpfx

theorem Mpfx.quantum_le_of_odd_rep {e : ℤ} {x : Dyadic}
    (hq : Dyadic.quantumAtLeast (e : QExp) x) {c q : ℤ}
    (hodd : Odd c) (heq : ((x : Dyadic) : ℝ) = (c : ℝ) * (2 : ℝ) ^ q) :
    e ≤ q := by sorry
