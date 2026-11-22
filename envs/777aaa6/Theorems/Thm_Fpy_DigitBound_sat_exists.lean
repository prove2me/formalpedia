-- Prove2me | Theorems.Thm_Fpy_DigitBound_sat_exists
-- name    : Fpy.DigitBound.sat_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:46:42.939186+00:00
-- url     : https://prove2.me/theorems/eb91afa8-16bf-48a9-a17f-c705e93b4134
-- title:
--   Digit Bound: sat exists
-- statement:
--   `Ψ` is satisfiable exactly when its encoding is.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L185-L186
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Encode.lean#L185-L186

import Definitions.Def_Fpy_DigitBound_Sound
import Definitions.Def_Fpy_DigitBound_Encode
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.sat_exists (Ψ : List Con) : (∃ ι, Sat ι Ψ) ↔ ∃ M : IModel, ∀ φ ∈ encode Ψ, φ.holds M := by sorry
