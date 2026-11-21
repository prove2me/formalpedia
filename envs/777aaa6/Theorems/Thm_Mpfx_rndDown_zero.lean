-- Prove2me | Theorems.Thm_Mpfx_rndDown_zero
-- name    : Mpfx.rndDown_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:45:53.852483+00:00
-- url     : https://prove2.me/theorems/369274d0-2f64-45af-9aed-8952495ba8cd
-- title:
--   Mpfx: rnd Down zero
-- statement:
--   The Mpfx construction uses the rnd Down zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L105-L106
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Rounding/Ulp.lean#L105-L106

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Mpfx_Rounding_Ulp
set_option autoImplicit true
open Mpfx

theorem Mpfx.rndDown_zero (F : FiniteFormat) : rndDown F 0 = 0 := by sorry
