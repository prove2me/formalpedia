-- Prove2me | Theorems.Thm_Fpy_DigitBound_Atom_holds_decode
-- name    : Fpy.DigitBound.Atom.holds_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:21.716683+00:00
-- url     : https://prove2.me/theorems/796bb389-5ed4-4387-8d34-1f69b181e81c
-- title:
--   Atom: holds decode
-- statement:
--   The Atom construction uses the holds decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L164-L170
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L164-L170

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.Atom.holds_decode (M : IModel) (a : Atom) : a.Holds M.decode ↔ a.enc.holds M := by sorry
