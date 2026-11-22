-- Prove2me | Theorems.Thm_Fpy_DigitBound_run_sound
-- name    : Fpy.DigitBound.run_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:43:51.936551+00:00
-- url     : https://prove2.me/theorems/979b7a66-0547-439d-acf9-f2c312a773b0
-- title:
--   Digit Bound: run sound
-- statement:
--   Constraint soundness for a program (D-Program): an argument described by `d`,
--   and by `a` for format inference, gives a result described by `d'`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L762-L775
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Sound.lean#L762-L775

import Definitions.Def_Fpy_DigitBound_Digits
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_DigitBound_Sound
import Theorems.Thm_Fpy_DigitBound_DEnv_Holds_single
import Theorems.Thm_Fpy_run_sound

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.run_sound (hA : A.Sound Φ) {f : Fn} {y : Var} {s : Stmt (fpy decode)} {d d' : DVal}
    {a : AVal D} {Δ' : DEnv} {Ψ : List Con} {n₀ n₁ : ℕ} (hΦ : Φ f = some (y, s))
    (hs : DExec decode Φ A (.single y d) (.single y a) (some .real) (some .real) [] n₀ s Δ'
      (some d') Ψ n₁) (hd : d.Below n₀) {ι : Asgn} {v v' : Val} (hv : Describes [] ι d v)
    (ha : Fpy.Describes a v) (hrun : Run Φ f v v') :
    ∃ ι', Agree n₀ ι ι' ∧ Sat ι' Ψ ∧ Describes Ψ ι' d' v' := by sorry
