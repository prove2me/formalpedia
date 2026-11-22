-- Prove2me | Theorems.Thm_Fpy_DigitBound_precision_of_precBound
-- name    : Fpy.DigitBound.precision_of_precBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:01.479351+00:00
-- url     : https://prove2.me/theorems/2a29798c-6b0d-4be0-9763-7e539511c2d0
-- title:
--   Digit Bound: precision of prec Bound
-- statement:
--   `precision_of_bound` with the bound given by `precBound`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L856-L862
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L856-L862

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

theorem Fpy.DigitBound.precision_of_precBound {p : ℕ} (hs : Sat ι Ψ)
    (hd : Describes Ψ ι (.num l m τ) (.num (.finite x)))
    (hp : precBound Ψ l m ≤ ((p : ℤ) : EInt)) : ∃ c e : ℤ, x = c * 2 ^ e ∧ |c| < 2 ^ p := by sorry
