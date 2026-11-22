-- Prove2me | Theorems.Thm_Fpy_reals_opAbs
-- name    : Fpy.reals_opAbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:27.873499+00:00
-- url     : https://prove2.me/theorems/b31061c3-954b-425f-906f-5a17f1147d39
-- title:
--   Fpy: reals op Abs
-- statement:
--   The Fpy construction uses the reals op Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L56-L59
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L56-L59

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_opAbs {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.abs u ∈ (Format.opAbs F).reals := by sorry
