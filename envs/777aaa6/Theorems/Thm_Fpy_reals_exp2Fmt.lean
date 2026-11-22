-- Prove2me | Theorems.Thm_Fpy_reals_exp2Fmt
-- name    : Fpy.reals_exp2Fmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:07.269752+00:00
-- url     : https://prove2.me/theorems/df268826-3502-474b-8076-8fc82c8597ee
-- title:
--   Fpy: reals exp2 Fmt
-- statement:
--   The Fpy construction uses the reals exp2 Fmt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L258-L300
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L258-L300

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_exp2Fmt {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.exp2 u ∈ (exp2Fmt F).γ := by sorry
