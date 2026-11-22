-- Prove2me | Theorems.Thm_Fpy_fpyAnalysis_sound
-- name    : Fpy.fpyAnalysis_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:14:21.127855+00:00
-- url     : https://prove2.me/theorems/235aa74d-ea6c-40b1-9ae8-42ac34237bc6
-- title:
--   Fpy: fpy Analysis sound
-- statement:
--   FPy's format inference meets every obligation of `Analysis.Sound`.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Analysis.lean#L105-L110
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Analysis.lean#L105-L110

import Definitions.Def_Fpy_FormatInference_Refine
import Definitions.Def_Fpy_FormatInference_Analysis
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}

theorem Fpy.fpyAnalysis_sound (Φ : Program (fpy decode)) : (fpyAnalysis decode c).Sound Φ := by sorry
