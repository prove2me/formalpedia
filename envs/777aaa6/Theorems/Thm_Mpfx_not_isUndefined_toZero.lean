-- Prove2me | Theorems.Thm_Mpfx_not_isUndefined_toZero
-- name    : Mpfx.not_isUndefined_toZero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:41:50.818827+00:00
-- url     : https://prove2.me/theorems/a64e3b67-8657-434d-9242-08b5ee2c5690
-- title:
--   Mpfx: not is Undefined to Zero
-- statement:
--   The Mpfx construction uses the not is Undefined to Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L162-L164
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Defs.lean#L162-L164

import Definitions.Def_Mpfx_Format_Parity
import Definitions.Def_Mpfx_Rounding_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.not_isUndefined_toZero (F : FiniteFormat) :
    ¬ F.IsUndefined .toZero := by sorry
