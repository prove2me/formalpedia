-- Prove2me | Theorems.Thm_Fpy_mem_liftCeil
-- name    : Fpy.mem_liftCeil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:21.140475+00:00
-- url     : https://prove2.me/theorems/3c6d1530-1590-4bed-979e-35e1f38af184
-- title:
--   Fpy: mem lift Ceil
-- statement:
--   The Fpy construction uses the mem lift Ceil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L365-L375
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L365-L375

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx
variable (c : Ceiling)
variable {c}

theorem Fpy.mem_liftCeil {f : Num → Num} {fa : Format → Fmt}
    (ha : ∀ {F u}, u ∈ F.reals → f u ∈ (fa F).γ) {F : Fmt} {u : Num} (hu : u ∈ F.γ) :
    f u ∈ (liftCeil c fa F).γ := by sorry
