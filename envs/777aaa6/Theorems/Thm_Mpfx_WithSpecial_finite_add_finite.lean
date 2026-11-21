-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_finite_add_finite
-- name    : Mpfx.WithSpecial.finite_add_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:47.868542+00:00
-- url     : https://prove2.me/theorems/ef799c25-4892-4cff-9d09-fc93c73e3b87
-- title:
--   With Special: finite add finite
-- statement:
--   The With Special construction uses the finite add finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L103-L104
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L103-L104

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.finite_add_finite (x y : Dyadic) :
    finite x + finite y = finite (x + y) := by sorry

attribute [defeq] Mpfx.WithSpecial.finite_add_finite
