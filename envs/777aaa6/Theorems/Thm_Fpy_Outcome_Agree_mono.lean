-- Prove2me | Theorems.Thm_Fpy_Outcome_Agree_mono
-- name    : Fpy.Outcome.Agree.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:52:49.875189+00:00
-- url     : https://prove2.me/theorems/9fa4a6f9-9e60-4743-873b-dffd0c0fd0c3
-- title:
--   Agree: mono
-- statement:
--   The Agree construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L84-L87
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Basic.lean#L84-L87

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Rewrite_Basic
set_option autoImplicit true
open Fpy
variable {L : Signature} {D : FormatDomain}
variable {X : Set Var}

theorem Fpy.Outcome.Agree.mono {Y : Set Var} {o o' : Outcome} (h : o.Agree X o') (hXY : X ⊆ Y) :
    o.Agree Y o' := by sorry
