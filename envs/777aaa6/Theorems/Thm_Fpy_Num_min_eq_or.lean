-- Prove2me | Theorems.Thm_Fpy_Num_min_eq_or
-- name    : Fpy.Num.min_eq_or
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:06:32.712704+00:00
-- url     : https://prove2.me/theorems/94ac5f5b-7ed7-4d93-8d67-a8221b3af489
-- title:
--   Num: min eq or
-- statement:
--   The Num construction uses the min eq or property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L147-L154
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Ops.lean#L147-L154

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Mpfx_Rounding_Op
import Definitions.Def_Fpy_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.Num.min_eq_or (u v : Num) : Num.min u v = u ∨ Num.min u v = v := by sorry
