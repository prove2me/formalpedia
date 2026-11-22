-- Prove2me | Theorems.Thm_Mpfx_Format_abs_subset_finite
-- name    : Mpfx.Format.abs_subset_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:32:15.915237+00:00
-- url     : https://prove2.me/theorems/157a1086-df5e-440c-b33f-53c2ed2dbd8a
-- title:
--   Format: abs subset finite
-- statement:
--   Finite form of `abs_subset`: `|F| ⊆ F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L380-L383
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L380-L383

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.abs_subset_finite (F : Format) :
    (Dyadic.abs '' F.toSet) ⊆ F.toSet := by sorry
