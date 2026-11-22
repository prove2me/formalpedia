-- Prove2me | Theorems.Thm_Fpy_DigitBound_describesAll_of_le
-- name    : Fpy.DigitBound.describesAll_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:18.317676+00:00
-- url     : https://prove2.me/theorems/b9d20690-f0b7-4ded-a04a-1b989e8feb31
-- title:
--   Digit Bound: describes All of le
-- statement:
--   D-List: each element, described by its own abstract value, is described by
--   the summary `d` once its fresh variables `[n₀, n₁)` are re-chosen.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L486-L495
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L486-L495

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.describesAll_of_le {n₀ n₁ : ℕ} {Ψ Ψ' : List Con} {d : DVal} {ι ι' : Asgn}
    (hb : Before n₀ Ψ) (hs : Sat ι Ψ) (h : Agree n₀ ι ι') :
    ∀ {ds : List DVal} {vs : List Val}, List.Forall₂ (Describes Ψ ι) ds vs →
      (∀ d' ∈ ds, DVal.Le n₀ n₁ Ψ Ψ' d' d) → DescribesAll (Ψ ++ Ψ') ι' d n₀ vs
  := by sorry
