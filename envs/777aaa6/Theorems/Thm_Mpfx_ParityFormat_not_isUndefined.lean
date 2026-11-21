-- Prove2me | Theorems.Thm_Mpfx_ParityFormat_not_isUndefined
-- name    : Mpfx.ParityFormat.not_isUndefined
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:41:50.170296+00:00
-- url     : https://prove2.me/theorems/7a460596-875b-4435-874c-dbdf2798c695
-- title:
--   Parity Format: not is Undefined
-- statement:
--   A parity format is never undefined: its invariant rules out `(1, ⊥)`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L180-L182
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L180-L182

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.ParityFormat.not_isUndefined (F : ParityFormat) (rm : RoundingMode) :
    ¬ F.IsUndefined rm := by sorry
