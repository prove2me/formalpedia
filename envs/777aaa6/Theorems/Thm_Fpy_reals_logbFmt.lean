-- Prove2me | Theorems.Thm_Fpy_reals_logbFmt
-- name    : Fpy.reals_logbFmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:11.832189+00:00
-- url     : https://prove2.me/theorems/de949a7e-7261-4fda-ac42-98d5e7615f6f
-- title:
--   Fpy: reals logb Fmt
-- statement:
--   The Fpy construction uses the reals logb Fmt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L188-L235
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L188-L235

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_logbFmt {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.logb u ∈ (logbFmt F).γ := by sorry
