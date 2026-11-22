-- Prove2me | Theorems.Thm_Fpy_DigitBound_DEnv_Holds_without
-- name    : Fpy.DigitBound.DEnv.Holds.without
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:17:57.804948+00:00
-- url     : https://prove2.me/theorems/757578d8-74e4-4d12-ac07-a7451e452035
-- title:
--   Holds: without
-- statement:
--   The Holds construction uses the without property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L255-L257
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L255-L257

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.DEnv.Holds.without {Δ : DEnv} {Ψ : List Con} {ι : Asgn} {σ : Store}
    (hσ : Δ.Holds Ψ ι σ) (X : List Var) : (Δ.without X).Holds Ψ ι σ := by sorry
