-- Prove2me | Theorems.Thm_Fpy_DigitBound_abs_le_of_grid
-- name    : Fpy.DigitBound.abs_le_of_grid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:42:56.420374+00:00
-- url     : https://prove2.me/theorems/50d0b0a9-f192-4415-8ee2-2e4a31c48345
-- title:
--   Digit Bound: abs le of grid
-- statement:
--   A multiple of `2^lo` below `2^(k+1)` is at most the run of ones `2^(k+1) − 2^lo`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L891-L900
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L891-L900

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

theorem Fpy.DigitBound.abs_le_of_grid {c lo k : ℤ} (h : |(c : ℝ) * 2 ^ lo| < 2 ^ (k + 1)) (hlo : lo ≤ k) :
    |(c : ℝ) * 2 ^ lo| ≤ 2 ^ (k + 1) - 2 ^ lo := by sorry
