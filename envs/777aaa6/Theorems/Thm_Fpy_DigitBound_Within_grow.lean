-- Prove2me | Theorems.Thm_Fpy_DigitBound_Within_grow
-- name    : Fpy.DigitBound.Within.grow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:43.671842+00:00
-- url     : https://prove2.me/theorems/56372076-0819-457d-944d-cfe2aceb92aa
-- title:
--   Within: grow
-- statement:
--   The Within construction uses the grow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L512-L516
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L512-L516

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.Within.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ')
    {ι ι' : Asgn} (h : Agree n ι ι') {Δ' : DEnv} {a : Option DVal} (hΔ : Δ'.Below n)
    (ha : RetBelow n a) : ∀ {o : Outcome}, Within Ψ ι Δ' a o → Within (Ψ ++ Ψ') ι' Δ' a o
  := by sorry
