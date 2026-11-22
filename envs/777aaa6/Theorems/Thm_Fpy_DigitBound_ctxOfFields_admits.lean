-- Prove2me | Theorems.Thm_Fpy_DigitBound_ctxOfFields_admits
-- name    : Fpy.DigitBound.ctxOfFields_admits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:21:55.937373+00:00
-- url     : https://prove2.me/theorems/aeefe812-b1a4-4911-97ef-150209aeb553
-- title:
--   Digit Bound: ctx Of Fields admits
-- statement:
--   The Digit Bound construction uses the ctx Of Fields admits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L411-L429
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Basic.lean#L411-L429

import Definitions.Def_Fpy_DigitBound_Defs
import Definitions.Def_Fpy_DigitBound_Basic
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
local notation "nan" => (WithSpecial.special Special.nan : Num)

theorem Fpy.DigitBound.ctxOfFields_admits {Ψ : List Con} {ι : Asgn} :
    ∀ {afs : List (Label × DVal)} {fs : List (Label × Val)} {ts : List (Label × Term)},
      DescribesFields Ψ ι afs fs → ctxOfFields afs = some ts →
      List.Forall₂ (fun (f : Label × Term) (w : Label × Val) =>
        f.1 = w.1 ∧ (w.2 = .num (numOfE (f.2.eval ι)) ∨ w.2 = .num nan)) ts fs
  := by sorry
