-- Prove2me | Theorems.Thm_Fpy_updates_of_not_mem
-- name    : Fpy.updates_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:29.412175+00:00
-- url     : https://prove2.me/theorems/0a6d743c-246d-48b1-b375-f1f248822055
-- title:
--   Fpy: updates of not mem
-- statement:
--   The Fpy construction uses the updates of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L75-L80
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L75-L80

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem Fpy.updates_of_not_mem {α : Type} {y : Var} :
    ∀ {f : Var → Option α} {ts : List Var} {xs : List α}, y ∉ ts → updates f ts xs y = f y := by sorry
