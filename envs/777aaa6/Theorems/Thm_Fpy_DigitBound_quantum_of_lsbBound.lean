-- Prove2me | Theorems.Thm_Fpy_DigitBound_quantum_of_lsbBound
-- name    : Fpy.DigitBound.quantum_of_lsbBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:42:48.842754+00:00
-- url     : https://prove2.me/theorems/701be127-9489-4326-bfc7-c8fc3231a708
-- title:
--   Digit Bound: quantum of lsb Bound
-- statement:
--   A value described under a solution lies on the grid `2^e` for `e ≤ lsbBound`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L865-L875
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L865-L875

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

theorem Fpy.DigitBound.quantum_of_lsbBound {e : ℤ} (hs : Sat ι Ψ)
    (hd : Describes Ψ ι (.num l m τ) (.num (.finite x))) (he : (e : EInt) ≤ lsbBound Ψ l m) :
    ∃ c : ℤ, x = c * 2 ^ e := by sorry
