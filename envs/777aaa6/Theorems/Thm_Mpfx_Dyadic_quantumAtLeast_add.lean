-- Prove2me | Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_add
-- name    : Mpfx.Dyadic.quantumAtLeast_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:28:01.162413+00:00
-- url     : https://prove2.me/theorems/38913e6a-469a-48a6-b5f8-3ecbadac0c27
-- title:
--   Dyadic: quantum At Least add
-- statement:
--   A sum of two quantum-aligned dyadics stays quantum-aligned.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L321-L331
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Dyadic.lean#L321-L331

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

theorem Mpfx.Dyadic.quantumAtLeast_add {e : QExp} {a b : Dyadic}
    (ha : Dyadic.quantumAtLeast e a) (hb : Dyadic.quantumAtLeast e b) :
    Dyadic.quantumAtLeast e (a + b) := by sorry
