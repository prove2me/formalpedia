-- Prove2me | Theorems.Thm_Mpfx_Format_neg_subset_finite
-- name    : Mpfx.Format.neg_subset_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:32:15.310507+00:00
-- url     : https://prove2.me/theorems/34fcc3bc-37a3-4c5e-8044-8bec427d4c22
-- title:
--   Format: neg subset finite
-- statement:
--   Finite form of `neg_subset`: `-F ⊆ F`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L372-L377
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L372-L377

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.neg_subset_finite (F : Format) : -F.toSet ⊆ F.toSet := by sorry
