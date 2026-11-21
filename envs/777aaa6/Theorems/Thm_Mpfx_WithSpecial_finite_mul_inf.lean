-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_finite_mul_inf
-- name    : Mpfx.WithSpecial.finite_mul_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:47.606246+00:00
-- url     : https://prove2.me/theorems/c4983d67-528a-464a-89a3-c14a3136c930
-- title:
--   With Special: finite mul inf
-- statement:
--   The With Special construction uses the finite mul inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L99-L101
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L99-L101

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.finite_mul_inf (x : Dyadic) (b : Bool) :
    finite x * special (.inf b) =
      if x = 0 then special .nan else special (.inf (xor b (decide ((x : ℚ) < 0)))) := by sorry

attribute [defeq] Mpfx.WithSpecial.finite_mul_inf
