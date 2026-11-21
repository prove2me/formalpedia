-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_inf_mul_inf
-- name    : Mpfx.WithSpecial.inf_mul_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:35.460066+00:00
-- url     : https://prove2.me/theorems/9aaa1c3c-3c86-4ef2-a360-1a4bcf1860a7
-- title:
--   With Special: inf mul inf
-- statement:
--   The With Special construction uses the inf mul inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L91-L93
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L91-L93

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.inf_mul_inf (a b : Bool) :
    (special (.inf a) : WithSpecial Dyadic) * special (.inf b) = special (.inf (xor a b)) := by sorry

attribute [defeq] Mpfx.WithSpecial.inf_mul_inf
