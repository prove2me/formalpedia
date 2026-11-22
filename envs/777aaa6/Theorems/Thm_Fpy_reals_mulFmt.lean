-- Prove2me | Theorems.Thm_Fpy_reals_mulFmt
-- name    : Fpy.reals_mulFmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:58.618455+00:00
-- url     : https://prove2.me/theorems/1a175642-c567-4847-b4ce-221bdeae7b34
-- title:
--   Fpy: reals mul Fmt
-- statement:
--   The Fpy construction uses the reals mul Fmt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L149-L164
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L149-L164

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_mulFmt {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.mul u v ∈ (mulFmt F₁ F₂).reals := by sorry
