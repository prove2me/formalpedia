-- Prove2me | Theorems.Thm_Mpfx_Format_add_subset
-- name    : Mpfx.Format.add_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:31:17.151374+00:00
-- url     : https://prove2.me/theorems/f1735bc5-d826-4fbb-9e0f-fa331cbe1830
-- title:
--   Format: add subset
-- statement:
--   **Add ⊆ inferred** (paper's `⊕`): the inferred format contains every IEEE sum, numeric
--   or special.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L470-L478
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L470-L478

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.add_subset (F₁ F₂ : Format) :
    F₁.values + F₂.values ⊆ (opAdd F₁ F₂).values := by sorry
