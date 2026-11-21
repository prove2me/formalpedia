-- Prove2me | Theorems.Thm_Mpfx_Format_neg_subset
-- name    : Mpfx.Format.neg_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:31:22.063687+00:00
-- url     : https://prove2.me/theorems/9a477a2b-3afe-4214-bf68-47293773ba8d
-- title:
--   Format: neg subset
-- statement:
--   **Neg ⊆ inferred**: the inferred format contains every negated value.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L481-L484
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Inference.lean#L481-L484

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise

theorem Mpfx.Format.neg_subset (F : Format) : -F.values ⊆ (opNeg F).values := by sorry
