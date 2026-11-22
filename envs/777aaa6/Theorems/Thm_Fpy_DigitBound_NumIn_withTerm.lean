-- Prove2me | Theorems.Thm_Fpy_DigitBound_NumIn_withTerm
-- name    : Fpy.DigitBound.NumIn.withTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:33.329692+00:00
-- url     : https://prove2.me/theorems/27034503-8409-4424-87a6-8b525a7fa975
-- title:
--   Num In: with Term
-- statement:
--   Interval and symbolic value together.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L381-L387
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L381-L387

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.NumIn.withTerm {ι : Asgn} {l m t : Term} {u : Num} (h : NumIn ι l m none u)
    (ht : u = nan ∨ u = numOfE (t.eval ι)) : NumIn ι l m (some t) u := by sorry
