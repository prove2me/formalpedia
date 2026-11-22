-- Prove2me | Theorems.Thm_Fpy_Num_mul_eq_finite
-- name    : Fpy.Num.mul_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:44.502768+00:00
-- url     : https://prove2.me/theorems/2ac40311-2578-4a33-a5f4-119bfaa3e27a
-- title:
--   Num: mul eq finite
-- statement:
--   The Num construction uses the mul eq finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L124-L130
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L124-L130

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.Num.mul_eq_finite {u v : Num} {x : ℝ} (h : Num.mul u v = .finite x) :
    ∃ a b, u = .finite a ∧ v = .finite b ∧ x = a * b := by sorry
