-- Prove2me | Theorems.Thm_Fpy_precisionAtMost_pHat
-- name    : Fpy.precisionAtMost_pHat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:31.429703+00:00
-- url     : https://prove2.me/theorems/d72f834f-190d-40e0-b8de-cd88b996a1dd
-- title:
--   Fpy: precision At Most p Hat
-- statement:
--   The Fpy construction uses the precision At Most p Hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L81-L97
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L81-L97

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.precisionAtMost_pHat {F : Format} {d : Mpfx.Dyadic} (hd : d ∈ F) :
    Dyadic.precisionAtMost F.pHat d := by sorry
