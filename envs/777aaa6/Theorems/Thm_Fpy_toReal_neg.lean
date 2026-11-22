-- Prove2me | Theorems.Thm_Fpy_toReal_neg
-- name    : Fpy.toReal_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:23.345896+00:00
-- url     : https://prove2.me/theorems/13ba6dc6-e37b-4b05-bdf8-cfd3309d844f
-- title:
--   Fpy: to Real neg
-- statement:
--   The Fpy construction uses the to Real neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L38-L39
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L38-L39

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg

set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.toReal_neg (u : WithSpecial Mpfx.Dyadic) : Num.neg u.toReal = (-u).toReal := by sorry
