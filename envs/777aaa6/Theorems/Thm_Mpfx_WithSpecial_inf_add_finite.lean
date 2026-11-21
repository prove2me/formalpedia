-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_inf_add_finite
-- name    : Mpfx.WithSpecial.inf_add_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:55.014055+00:00
-- url     : https://prove2.me/theorems/c22f67b5-abc1-426c-82fd-c616abf6dd93
-- title:
--   With Special: inf add finite
-- statement:
--   The With Special construction uses the inf add finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L117-L118
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L117-L118

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.inf_add_finite (a : Bool) (y : Dyadic) :
    (special (.inf a) : WithSpecial Dyadic) + finite y = special (.inf a) := by sorry

attribute [defeq] Mpfx.WithSpecial.inf_add_finite
