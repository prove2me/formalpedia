-- Prove2me | Theorems.Thm_Fpy_DigitBound_abs_lt_of_msbBound
-- name    : Fpy.DigitBound.abs_lt_of_msbBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:15.780435+00:00
-- url     : https://prove2.me/theorems/e09b877c-e129-49bf-b584-7f6bf242815f
-- title:
--   Digit Bound: abs lt of msb Bound
-- statement:
--   A value described under a solution is below `2^(k+1)` for `msbBound ≤ k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L878-L888
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L878-L888

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

theorem Fpy.DigitBound.abs_lt_of_msbBound {k : ℤ} (hs : Sat ι Ψ)
    (hd : Describes Ψ ι (.num l m τ) (.num (.finite x))) (hk : msbBound Ψ m ≤ k) :
    |x| < 2 ^ (k + 1) := by sorry
