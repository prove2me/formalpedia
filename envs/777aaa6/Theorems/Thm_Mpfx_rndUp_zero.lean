-- Prove2me | Theorems.Thm_Mpfx_rndUp_zero
-- name    : Mpfx.rndUp_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:45:56.964756+00:00
-- url     : https://prove2.me/theorems/7862b9cd-f315-4ee6-a3f8-c749a5cdda75
-- title:
--   Mpfx: rnd Up zero
-- statement:
--   The Mpfx construction uses the rnd Up zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L135-L136
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L135-L136

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndUp_zero (F : FiniteFormat) : rndUp F 0 = 0 := by sorry
