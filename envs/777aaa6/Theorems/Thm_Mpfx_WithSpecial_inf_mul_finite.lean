-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_inf_mul_finite
-- name    : Mpfx.WithSpecial.inf_mul_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:39.720656+00:00
-- url     : https://prove2.me/theorems/d1a19665-e01d-43b2-83f0-c06c7fc1b668
-- title:
--   With Special: inf mul finite
-- statement:
--   The With Special construction uses the inf mul finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L95-L97
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L95-L97

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.inf_mul_finite (a : Bool) (y : Dyadic) :
    (special (.inf a) : WithSpecial Dyadic) * finite y =
      if y = 0 then special .nan else special (.inf (xor a (decide ((y : ℚ) < 0)))) := by sorry

attribute [defeq] Mpfx.WithSpecial.inf_mul_finite
