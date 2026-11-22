-- Prove2me | Theorems.Thm_Fpy_DigitBound_precision_of_bound
-- name    : Fpy.DigitBound.precision_of_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:17.315867+00:00
-- url     : https://prove2.me/theorems/df23416e-88d9-4eb2-b330-2dfea48b09b3
-- title:
--   Digit Bound: precision of bound
-- statement:
--   A finite value described by `⟨[l, m], _⟩` under `ι`, where
--   `m ≤ l + p − 1`, has at most `p` significant digits.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L781-L804
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L781-L804

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.precision_of_bound {Ψ : List Con} {ι : Asgn} {l m : Term} {τ : Option Term} {x : ℝ}
    {p : ℕ} (hd : Describes Ψ ι (.num l m τ) (.num (.finite x)))
    (hp : m.eval ι ≤ l.eval ι + ((p - 1 : ℤ) : EInt)) :
    ∃ c e : ℤ, x = c * 2 ^ e ∧ |c| < 2 ^ p := by sorry
