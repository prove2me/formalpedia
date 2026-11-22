-- Prove2me | Theorems.Thm_Fpy_DigitBound_decode_ofAsgn
-- name    : Fpy.DigitBound.decode_ofAsgn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:04.152261+00:00
-- url     : https://prove2.me/theorems/97ef357a-af93-4b99-b2c2-81605602e5d7
-- title:
--   Digit Bound: decode of Asgn
-- statement:
--   The Digit Bound construction uses the decode of Asgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L80-L83
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L80-L83

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.decode_ofAsgn (ι : Asgn) : (IModel.ofAsgn ι).decode = ι := by sorry
