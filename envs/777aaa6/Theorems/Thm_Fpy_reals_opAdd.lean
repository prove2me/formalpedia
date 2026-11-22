-- Prove2me | Theorems.Thm_Fpy_reals_opAdd
-- name    : Fpy.reals_opAdd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:12:21.193171+00:00
-- url     : https://prove2.me/theorems/3685f909-c384-462d-833e-5954b7647fd7
-- title:
--   Fpy: reals op Add
-- statement:
--   The Fpy construction uses the reals op Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L45-L49
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Ops.lean#L45-L49

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
set_option autoImplicit true
open Fpy
open Mpfx

theorem Fpy.reals_opAdd {F₁ F₂ : Format} {u v : Num} (hu : u ∈ F₁.reals) (hv : v ∈ F₂.reals) :
    Num.add u v ∈ (Format.opAdd F₁ F₂).reals := by sorry
