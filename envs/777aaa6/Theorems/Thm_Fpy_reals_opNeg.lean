-- Prove2me | Theorems.Thm_Fpy_reals_opNeg
-- name    : Fpy.reals_opNeg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:35.499575+00:00
-- url     : https://prove2.me/theorems/981e24b2-1861-4f04-aa42-c4297d327195
-- title:
--   Fpy: reals op Neg
-- statement:
--   The Fpy construction uses the reals op Neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L51-L54
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L51-L54

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_opNeg {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.neg u ∈ (Format.opNeg F).reals := by sorry
