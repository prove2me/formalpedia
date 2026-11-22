-- Prove2me | Theorems.Thm_Fpy_DigitBound_ctxOfFields_below
-- name    : Fpy.DigitBound.ctxOfFields_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:00.67299+00:00
-- url     : https://prove2.me/theorems/48d3d090-581d-42d8-86bf-952d42f0441f
-- title:
--   Digit Bound: ctx Of Fields below
-- statement:
--   The Digit Bound construction uses the ctx Of Fields below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L441-L459
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L441-L459

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.ctxOfFields_below {n : ℕ} :
    ∀ {afs : List (Label × DVal)} {ts : List (Label × Term)}, DVal.BelowFields n afs →
      ctxOfFields afs = some ts → ∀ f ∈ ts, f.2.Below n
  := by sorry
