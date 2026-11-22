-- Prove2me | Theorems.Thm_P2M_Mpfx_nearest_eq_of_close__390f66b23c83
-- name    : P2M_Mpfx_nearest_eq_of_close__390f66b23c83
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:54:08.318044+00:00
-- url     : https://prove2.me/theorems/0f346bf8-3be9-48aa-92d9-33ebd48e0ea0
-- title:
--   P2 M Mpfx nearest eq of close  390f66b23c83: P2 M Mpfx nearest eq of close  390f66b23c83
-- statement:
--   Dyadic form of `nearest_eq_of_close`: if `g` is a multiple of `v`'s step
--   (`quantumAtLeast (canonicalExp v) g`) and `|v − g| < ½·ulp F v`, then `g`
--   is the nearest rounding of `v`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L229-L250
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L229-L250

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem P2M_Mpfx_nearest_eq_of_close__390f66b23c83 (F : FiniteFormat) (tb : TieBreak) (v : ℝ)
    (hundef : ¬ F.IsUndefined (.nearest tb)) {g : _root_.Mpfx.Dyadic}
    (hg : _root_.Mpfx.Dyadic.quantumAtLeast ((F.canonicalExp v : ℤ) : QExp) g)
    (hclose : |v - (g : ℝ)| < (2 : ℝ) ^ (F.canonicalExp v) / 2) :
    RoundsFinite F.unbounded (.nearest tb) v g := by sorry

alias «Mpfx».«nearest_eq_of_close'» := P2M_Mpfx_nearest_eq_of_close__390f66b23c83
