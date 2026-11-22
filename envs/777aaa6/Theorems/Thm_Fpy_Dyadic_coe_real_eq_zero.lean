-- Prove2me | Theorems.Thm_Fpy_Dyadic_coe_real_eq_zero
-- name    : Fpy.Dyadic.coe_real_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:11:19.389311+00:00
-- url     : https://prove2.me/theorems/84d450e0-5c08-416f-9948-48485bf6e9f7
-- title:
--   Dyadic: coe real eq zero
-- statement:
--   The Dyadic construction uses the coe real eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L21-L22
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L21-L22

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.Dyadic.coe_real_eq_zero {d : Mpfx.Dyadic} : (d : ℝ) = 0 ↔ d = 0 := by sorry
