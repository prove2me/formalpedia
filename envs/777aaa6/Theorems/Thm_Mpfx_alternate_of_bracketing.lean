-- Prove2me | Theorems.Thm_Mpfx_alternate_of_bracketing
-- name    : Mpfx.alternate_of_bracketing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:51:43.585762+00:00
-- url     : https://prove2.me/theorems/f178707d-c1c0-415c-920c-34d55228b747
-- title:
--   Mpfx: alternate of bracketing
-- statement:
--   `neighbors_alternate`, stated over the round-down/round-up specs.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L484-L501
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Basic.lean#L484-L501

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
set_option autoImplicit true
open Mpfx

theorem Mpfx.alternate_of_bracketing {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y y' : Dyadic}
    (hy : RoundsFinite F.unbounded .toNegative x y)
    (hy' : RoundsFinite F.unbounded .toPositive x y')
    (hne : x ≠ (y : ℝ)) :
    (F.IsOdd y' ↔ ¬ F.IsOdd y) ∧ (¬ F.IsEven y → F.IsEven y') := by sorry
