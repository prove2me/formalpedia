-- Prove2me | Theorems.Thm_Fpy_DigitBound_DEnv_Holds_grow
-- name    : Fpy.DigitBound.DEnv.Holds.grow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:58.156093+00:00
-- url     : https://prove2.me/theorems/cc41468c-3cbc-4034-a734-6d6c4089c7f7
-- title:
--   Holds: grow
-- statement:
--   The Holds construction uses the grow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L242-L246
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L242-L246

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.DEnv.Holds.grow {n n' : ℕ} {Ψ Ψ' : List Con} (hb : Before n Ψ) (hF : Fresh n n' Ψ')
    {ι ι' : Asgn} (h : Agree n ι ι') {Δ : DEnv} {σ : Store} (hΔ : Δ.Below n)
    (hσ : Δ.Holds Ψ ι σ) : Δ.Holds (Ψ ++ Ψ') ι' σ := by sorry
