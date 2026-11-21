-- Prove2me | Theorems.Thm_Mpfx_Format_mul_subset_finite
-- name    : Mpfx.Format.mul_subset_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:30:51.70992+00:00
-- url     : https://prove2.me/theorems/9886ebb7-4f9a-4fb2-8ab0-de2a9c63fcf8
-- title:
--   Format: mul subset finite
-- statement:
--   Finite form of `mul_subset`: `{x · y | x ∈ F₁, y ∈ F₂} ⊆ opMul F₁ F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L239-L265
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L239-L265

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.mul_subset_finite (F₁ F₂ : Format) :
    F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂).toSet := by sorry
