-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_inf_add_inf
-- name    : Mpfx.WithSpecial.inf_add_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:52.315951+00:00
-- url     : https://prove2.me/theorems/4a254258-57c9-4ac4-936a-0fcac76cf36d
-- title:
--   With Special: inf add inf
-- statement:
--   The With Special construction uses the inf add inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L113-L115
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L113-L115

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.inf_add_inf (a b : Bool) :
    (special (.inf a) : WithSpecial Dyadic) + special (.inf b) =
      if a = b then special (.inf a) else special .nan := by sorry

attribute [defeq] Mpfx.WithSpecial.inf_add_inf
