-- Prove2me | Theorems.Thm_Fpy_Num_max_eq_or
-- name    : Fpy.Num.max_eq_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:29.729535+00:00
-- url     : https://prove2.me/theorems/ed054384-9757-4058-bb90-04294f448372
-- title:
--   Num: max eq or
-- statement:
--   The Num construction uses the max eq or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L156-L163
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L156-L163

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.Num.max_eq_or (u v : Num) : Num.max u v = u ∨ Num.max u v = v := by sorry
