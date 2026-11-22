-- Prove2me | Theorems.Thm_Fpy_DigitBound_sat_decode
-- name    : Fpy.DigitBound.sat_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:38.684521+00:00
-- url     : https://prove2.me/theorems/971c9b2f-3fca-4cb6-b4ff-cdee21c27b61
-- title:
--   Digit Bound: sat decode
-- statement:
--   The Digit Bound construction uses the sat decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L175-L178
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L175-L178

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.sat_decode (M : IModel) (Ψ : List Con) :
    Sat M.decode Ψ ↔ ∀ φ ∈ encode Ψ, φ.holds M := by sorry
