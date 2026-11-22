-- Prove2me | Theorems.Thm_Fpy_ctxOfAVal_sound
-- name    : Fpy.ctxOfAVal_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:14:25.280039+00:00
-- url     : https://prove2.me/theorems/691d1b0f-d2c0-4875-b758-eaed6a0074a0
-- title:
--   Fpy: ctx Of AVal sound
-- statement:
--   The Fpy construction uses the ctx Of AVal sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Analysis.lean#L85-L93
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Analysis.lean#L85-L93

import Definitions.Def_Fpy_FormatInference_Refine
import Definitions.Def_Fpy_FormatInference_Analysis
set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {c : Ceiling}

theorem Fpy.ctxOfAVal_sound {a : AVal (Fmt.domain c)} {C : Val} {fs : List (Label × Val)}
    (hC : ctxOfAVal a = some C) (ha : Describes a (.record fs)) : C = .ctx fs := by sorry
