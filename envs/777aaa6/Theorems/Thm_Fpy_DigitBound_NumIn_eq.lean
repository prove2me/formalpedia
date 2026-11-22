-- Prove2me | Theorems.Thm_Fpy_DigitBound_NumIn_eq
-- name    : Fpy.DigitBound.NumIn.eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:16:08.005188+00:00
-- url     : https://prove2.me/theorems/58dceab9-8b98-44f3-a9e7-2829b1228f7e
-- title:
--   Num In: eq
-- statement:
--   The Num In construction uses the eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L281-L283
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L281-L283

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.NumIn.eq {ι : Asgn} {l m : Term} {τ : Option Term} {u : Num} (h : NumIn ι l m τ u)
    (hu : u ≠ nan) : lsbOf u = l.eval ι ∧ msbOf u = m.eval ι := by sorry
