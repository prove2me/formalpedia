-- Prove2me | Theorems.Thm_Mpfx_not_isUndefined_toNegative
-- name    : Mpfx.not_isUndefined_toNegative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:48:20.69638+00:00
-- url     : https://prove2.me/theorems/1ad42e95-094c-49a7-a7ab-217b868c3368
-- title:
--   Mpfx: not is Undefined to Negative
-- statement:
--   Directed modes are never undefined.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L171-L173
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L171-L173

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.not_isUndefined_toNegative (F : FiniteFormat) :
    ¬ F.IsUndefined .toNegative := by sorry
