-- Prove2me | Theorems.Thm_Fpy_DigitBound_eval_update
-- name    : Fpy.DigitBound.eval_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:58.864678+00:00
-- url     : https://prove2.me/theorems/0d6ff91d-002b-4b2b-8640-d62fd16656bd
-- title:
--   Digit Bound: eval update
-- statement:
--   The Digit Bound construction uses the eval update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L285-L287
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L285-L287

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.eval_update {n : ℕ} {t : Term} (h : t.Below n) (ι : Asgn) (z : EInt) :
    t.eval (Function.update ι n z) = t.eval ι := by sorry
