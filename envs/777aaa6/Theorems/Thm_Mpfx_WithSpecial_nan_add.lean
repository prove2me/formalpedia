-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_nan_add
-- name    : Mpfx.WithSpecial.nan_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:54.461855+00:00
-- url     : https://prove2.me/theorems/df1b049b-6e06-4ae3-8d0f-e51ae03fd2b3
-- title:
--   With Special: nan add
-- statement:
--   The With Special construction uses the nan add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L106-L108
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L106-L108

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.nan_add (v : WithSpecial Dyadic) :
    (special .nan : WithSpecial Dyadic) + v = special .nan := by sorry
