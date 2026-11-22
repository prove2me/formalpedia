-- Prove2me | Theorems.Thm_Fpy_Num_sqrt_eq_finite
-- name    : Fpy.Num.sqrt_eq_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:47.401186+00:00
-- url     : https://prove2.me/theorems/69cd8897-9379-48ed-8943-1f025f1c2db2
-- title:
--   Num: sqrt eq finite
-- statement:
--   The Num construction uses the sqrt eq finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L141-L145
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L141-L145

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.Num.sqrt_eq_finite {u : Num} {x : ℝ} (h : Num.sqrt u = .finite x) :
    ∃ a, u = .finite a ∧ 0 ≤ a ∧ x = Real.sqrt a := by sorry
