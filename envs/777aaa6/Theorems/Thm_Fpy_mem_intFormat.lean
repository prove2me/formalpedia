-- Prove2me | Theorems.Thm_Fpy_mem_intFormat
-- name    : Fpy.mem_intFormat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:34.334737+00:00
-- url     : https://prove2.me/theorems/37203b75-de95-45cf-a866-5e766dbc6a8b
-- title:
--   Fpy: mem int Format
-- statement:
--   The Fpy construction uses the mem int Format property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L437-L439
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L437-L439

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.mem_intFormat (n : ℕ) : (.finite (n : ℝ) : Num) ∈ intFormat.reals := by sorry
