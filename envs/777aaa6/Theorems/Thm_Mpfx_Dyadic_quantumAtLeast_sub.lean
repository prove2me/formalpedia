-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_sub
-- name    : Mpfx.Dyadic.quantumAtLeast_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:29:39.381925+00:00
-- url     : https://prove2.me/theorems/ffa7dbeb-bef0-4acf-a3c2-a94321e40e71
-- title:
--   Dyadic: quantum At Least sub
-- statement:
--   A difference of two quantum-aligned dyadics stays quantum-aligned.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L334-L337
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L334-L337

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
open Mpfx.Dyadic

theorem Mpfx.Dyadic.quantumAtLeast_sub {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a - b) := by sorry
