-- Prove2me | Theorems.Thm_Fpy_DigitBound_format_of_bounds
-- name    : Fpy.DigitBound.format_of_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:24.152695+00:00
-- url     : https://prove2.me/theorems/8d4ca59c-ea34-4f46-8cff-2d9ae918c231
-- title:
--   Digit Bound: format of bounds
-- statement:
--   The format of §4.3's second pass: a finite value described under a solution lies in
--   `A(p, e, 2^(k+1) − 2^max(e, k − p + 1))` for `prec♮ ≤ p`, `e ≤ lsbBound` and
--   `msbBound ≤ k`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L943-L953
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L943-L953

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

theorem Fpy.DigitBound.format_of_bounds {p : ℕ} {e k : ℤ} (hs : Sat ι Ψ)
    (hd : Describes Ψ ι (.num l m τ) (.num (.finite x)))
    (hp : precBound Ψ l m ≤ ((p : ℤ) : EInt)) (he : (e : EInt) ≤ lsbBound Ψ l m)
    (hk : msbBound Ψ m ≤ k) (hek : e ≤ k) (hp1 : 1 ≤ p) :
    (∃ c e' : ℤ, x = c * 2 ^ e' ∧ |c| < 2 ^ p) ∧ (∃ c : ℤ, x = c * 2 ^ e) ∧
      |x| ≤ 2 ^ (k + 1) - 2 ^ max e (k - p + 1) := by sorry
