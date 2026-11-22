-- Prove2me | Theorems.Thm_Fpy_reals_addFmt
-- name    : Fpy.reals_addFmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:03.232855+00:00
-- url     : https://prove2.me/theorems/58d49f1a-865b-4bbc-80b4-4fd7418799fd
-- title:
--   Fpy: reals add Fmt
-- statement:
--   The Fpy construction uses the reals add Fmt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L141-L143
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L141-L143

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_addFmt {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.add u v ∈ (addFmt F₁ F₂).reals := by sorry
