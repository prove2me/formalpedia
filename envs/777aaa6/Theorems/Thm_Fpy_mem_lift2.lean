-- Prove2me | Theorems.Thm_Fpy_mem_lift2
-- name    : Fpy.mem_lift2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:34.461548+00:00
-- url     : https://prove2.me/theorems/10a8a155-b4ed-499f-89fb-20f059b5966b
-- title:
--   Fpy: mem lift2
-- statement:
--   The Fpy construction uses the mem lift2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L339-L354
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L339-L354

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx
variable (c : Ceiling)
variable {c}

theorem Fpy.mem_lift2 {f : Num → Num → Num} {fa : Format → Format → Fmt}
    (ha : ∀ {F₁ F₂ u v}, u ∈ F₁.reals → v ∈ F₂.reals → f u v ∈ (fa F₁ F₂).γ)
    {F₁ F₂ : Fmt} {u v : Num} (hu : u ∈ F₁.γ) (hv : v ∈ F₂.γ) :
    f u v ∈ (lift2 c f fa F₁ F₂).γ := by sorry
