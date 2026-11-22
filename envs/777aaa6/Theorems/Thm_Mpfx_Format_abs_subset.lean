-- Prove2me | Theorems.Thm_Mpfx_Format_abs_subset
-- name    : Mpfx.Format.abs_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:31:21.815062+00:00
-- url     : https://prove2.me/theorems/ff6b7cad-7e64-4234-906b-f8712bd9ba8b
-- title:
--   Format: abs subset
-- statement:
--   **Abs ⊆ inferred**: the inferred format contains every IEEE absolute
--   value, numeric or special.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L514-L523
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L514-L523

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.abs_subset (F : Format) :
    WithSpecial.abs '' F.values ⊆ (opAbs F).values := by sorry
