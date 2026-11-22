-- Prove2me | Theorems.Thm_Fpy_DigitBound_Term_ne_bot_decode
-- name    : Fpy.DigitBound.Term.ne_bot_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:40.846735+00:00
-- url     : https://prove2.me/theorems/440f7e24-2811-48d2-af89-818824943a37
-- title:
--   Term: ne bot decode
-- statement:
--   The Term construction uses the ne bot decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L188-L193
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L188-L193

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.Term.ne_bot_decode (M : IModel) (t : Term) :
    t.eval M.decode ≠ ⊥ ↔ t.enc.bot.holds M = false := by sorry
