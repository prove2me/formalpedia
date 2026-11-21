-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_add_nan
-- name    : Mpfx.WithSpecial.add_nan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:23:56.443953+00:00
-- url     : https://prove2.me/theorems/09402226-1fe5-4cc3-8467-c7fbf8b2e6d2
-- title:
--   With Special: add nan
-- statement:
--   The With Special construction uses the add nan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L110-L111
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L110-L111

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.WithSpecial

theorem Mpfx.WithSpecial.add_nan (u : WithSpecial Dyadic) : u + special .nan = special .nan := by sorry
