-- Prove2me | Theorems.Thm_Fpy_Num_add_eq_finite
-- name    : Fpy.Num.add_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:27.162481+00:00
-- url     : https://prove2.me/theorems/78dc38f9-6f24-4639-b795-7d7399c0161c
-- title:
--   Num: add eq finite
-- statement:
--   The Num construction uses the add eq finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L116-L122
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L116-L122

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.Num.add_eq_finite {u v : Num} {x : ℝ} (h : Num.add u v = .finite x) :
    ∃ a b, u = .finite a ∧ v = .finite b ∧ x = a + b := by sorry
