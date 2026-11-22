-- Prove2me | Theorems.Thm_Fpy_DigitBound_le_of_width
-- name    : Fpy.DigitBound.le_of_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:14.420899+00:00
-- url     : https://prove2.me/theorems/edbe0499-ece0-4c7e-a48e-c774d9b9f95c
-- title:
--   Digit Bound: le of width
-- statement:
--   The Digit Bound construction uses the le of width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L806-L820
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L806-L820

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.le_of_width {a b : EInt} {p : ℤ} (h : a + negE b + ((1 : ℤ) : EInt) ≤ p) :
    a ≤ b + ((p - 1 : ℤ) : EInt) := by sorry
