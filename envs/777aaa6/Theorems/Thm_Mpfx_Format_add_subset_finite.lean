-- Prove2me | Theorems.Thm_Mpfx_Format_add_subset_finite
-- name    : Mpfx.Format.add_subset_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:31:02.170059+00:00
-- url     : https://prove2.me/theorems/b6d6f46b-426a-473d-9c88-8f167cfe1e2e
-- title:
--   Format: add subset finite
-- statement:
--   Finite form of `add_subset`: `{x + y | x ∈ F₁, y ∈ F₂} ⊆ opAdd F₁ F₂`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L319-L369
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L319-L369

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.add_subset_finite (F₁ F₂ : Format) :
    F₁.toSet + F₂.toSet ⊆ (opAdd F₁ F₂).toSet := by sorry
