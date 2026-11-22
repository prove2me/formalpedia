-- Prove2me | Theorems.Thm_Fpy_DigitBound_sat_iff
-- name    : Fpy.DigitBound.sat_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:44:13.470226+00:00
-- url     : https://prove2.me/theorems/550eb8a6-1b3d-4f6b-beae-398b6aafdad1
-- title:
--   Digit Bound: sat iff
-- statement:
--   The Digit Bound construction uses the sat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L180-L182
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L180-L182

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.sat_iff (ι : Asgn) (Ψ : List Con) :
    Sat ι Ψ ↔ ∀ φ ∈ encode Ψ, φ.holds (IModel.ofAsgn ι) := by sorry
