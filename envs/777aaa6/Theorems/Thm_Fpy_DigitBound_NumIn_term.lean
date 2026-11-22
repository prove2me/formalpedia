-- Prove2me | Theorems.Thm_Fpy_DigitBound_NumIn_term
-- name    : Fpy.DigitBound.NumIn.term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:18:52.408406+00:00
-- url     : https://prove2.me/theorems/e75a16bb-0279-4052-9b55-cbb275401494
-- title:
--   Num In: term
-- statement:
--   The Num In construction uses the term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L393-L395
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L393-L395

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.NumIn.term {ι : Asgn} {l m t : Term} {u : Num} (h : NumIn ι l m (some t) u) :
    u = nan ∨ u = numOfE (t.eval ι) := by sorry
