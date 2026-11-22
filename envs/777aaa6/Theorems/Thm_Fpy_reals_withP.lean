-- Prove2me | Theorems.Thm_Fpy_reals_withP
-- name    : Fpy.reals_withP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:47.701526+00:00
-- url     : https://prove2.me/theorems/caaf6a33-1ee4-48e4-8d09-64c88bdd760b
-- title:
--   Fpy: reals with P
-- statement:
--   The Fpy construction uses the reals with P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L66-L69
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L66-L69

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_withP {F : Format} {p : Prec} (h : F.p ≤ p) {u : Num} (hu : u ∈ F.reals) :
    u ∈ (F.withP p).reals := by sorry
