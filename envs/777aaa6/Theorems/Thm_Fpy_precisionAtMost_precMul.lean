-- Prove2me | Theorems.Thm_Fpy_precisionAtMost_precMul
-- name    : Fpy.precisionAtMost_precMul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:54.056164+00:00
-- url     : https://prove2.me/theorems/267fcf5e-12b6-4f03-8ac2-cb57da67c97a
-- title:
--   Fpy: precision At Most prec Mul
-- statement:
--   The Fpy construction uses the precision At Most prec Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L123-L133
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L123-L133

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.precisionAtMost_precMul {q₁ q₂ : Prec} {x y : Mpfx.Dyadic}
    (hx : Dyadic.precisionAtMost q₁ x) (hy : Dyadic.precisionAtMost q₂ y) :
    Dyadic.precisionAtMost (precMul q₁ q₂) (x * y) := by sorry
