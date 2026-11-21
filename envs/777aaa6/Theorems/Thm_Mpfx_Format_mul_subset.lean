-- Prove2me | Theorems.Thm_Mpfx_Format_mul_subset
-- name    : Mpfx.Format.mul_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:31:08.059726+00:00
-- url     : https://prove2.me/theorems/c1741f19-74f6-445a-a1a3-1b55ddd73fea
-- title:
--   Format: mul subset
-- statement:
--   **Mul ⊆ inferred** (paper's `⊗`): the inferred format contains every IEEE product,
--   numeric or special.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L427-L435
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L427-L435

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.mul_subset (F₁ F₂ : Format) :
    F₁.values * F₂.values ⊆ (opMul F₁ F₂).values := by sorry
