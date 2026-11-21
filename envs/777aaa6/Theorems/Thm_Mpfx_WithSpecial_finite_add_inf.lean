-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_finite_add_inf
-- name    : Mpfx.WithSpecial.finite_add_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:24:00.221701+00:00
-- url     : https://prove2.me/theorems/2a7528c5-aeaf-41f8-bec0-80d1450835c9
-- title:
--   With Special: finite add inf
-- statement:
--   The With Special construction uses the finite add inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L120-L121
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L120-L121

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.finite_add_inf (x : Dyadic) (b : Bool) :
    finite x + special (.inf b) = special (.inf b) := by sorry

attribute [defeq] Mpfx.WithSpecial.finite_add_inf
