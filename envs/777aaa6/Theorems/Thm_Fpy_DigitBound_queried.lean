-- Prove2me | Theorems.Thm_Fpy_DigitBound_queried
-- name    : Fpy.DigitBound.queried
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:42:33.578767+00:00
-- url     : https://prove2.me/theorems/a7e705b7-f369-40d4-becb-4b888bc65422
-- title:
--   Digit Bound: queried
-- statement:
--   A solution describing a finite nonzero value is queried.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L847-L853
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L847-L853

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)
variable {Ψ : List Con} {ι : Asgn} {l m : Term} {τ : Option Term} {x : ℝ}

theorem Fpy.DigitBound.queried (hs : Sat ι Ψ) (hd : Describes Ψ ι (.num l m τ) (.num (.finite x)))
    (h0 : x ≠ 0) : Queried Ψ m ι := by sorry
