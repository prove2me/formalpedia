-- Prove2me | Theorems.Thm_Fpy_DigitBound_bound_of_msbBound
-- name    : Fpy.DigitBound.bound_of_msbBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:42:35.873634+00:00
-- url     : https://prove2.me/theorems/0de465f5-0768-47e8-af25-8fe40ebf62e4
-- title:
--   Digit Bound: bound of msb Bound
-- statement:
--   The bound `b`, tightened by the grid or the precision: a value described under a
--   solution, with `msbBound ≤ k`, is at most `2^(k+1) − 2^lo` for `lo ≤ k` with
--   `lo ≤ lsbBound` or `prec♮ ≤ k − lo + 1`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L905-L938
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L905-L938

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

theorem Fpy.DigitBound.bound_of_msbBound {k lo : ℤ} (hs : Sat ι Ψ)
    (hd : Describes Ψ ι (.num l m τ) (.num (.finite x))) (hk : msbBound Ψ m ≤ k)
    (hlo : lo ≤ k)
    (h : (lo : EInt) ≤ lsbBound Ψ l m ∨ precBound Ψ l m ≤ ((k - lo + 1 : ℤ) : EInt)) :
    |x| ≤ 2 ^ (k + 1) - 2 ^ lo := by sorry
