-- Prove2me | Theorems.Thm_Fpy_mem_lift1
-- name    : Fpy.mem_lift1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:13:34.1818+00:00
-- url     : https://prove2.me/theorems/cfef5162-c8a4-44e9-9c3b-576d78fecb0a
-- title:
--   Fpy: mem lift1
-- statement:
--   The Fpy construction uses the mem lift1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L356-L363
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L356-L363

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx
variable (c : Ceiling)
variable {c}

theorem Fpy.mem_lift1 {f : Num → Num} {fa : Format → Fmt}
    (ha : ∀ {F u}, u ∈ F.reals → f u ∈ (fa F).γ) {F : Fmt} {u : Num} (hu : u ∈ F.γ) :
    f u ∈ (lift1 f fa F).γ := by sorry
