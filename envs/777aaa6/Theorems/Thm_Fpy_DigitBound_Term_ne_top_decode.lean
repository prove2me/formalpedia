-- Prove2me | Theorems.Thm_Fpy_DigitBound_Term_ne_top_decode
-- name    : Fpy.DigitBound.Term.ne_top_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:41.023813+00:00
-- url     : https://prove2.me/theorems/eaac5123-6cfc-4ffa-a86a-27b53360c41f
-- title:
--   Term: ne top decode
-- statement:
--   The Term construction uses the ne top decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L195-L200
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L195-L200

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.Term.ne_top_decode (M : IModel) (t : Term) :
    t.eval M.decode ≠ ⊤ ↔ t.enc.top.holds M = false := by sorry
