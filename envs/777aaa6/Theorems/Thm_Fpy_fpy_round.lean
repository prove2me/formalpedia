-- Prove2me | Theorems.Thm_Fpy_fpy_round
-- name    : Fpy.fpy_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:37:58.347955+00:00
-- url     : https://prove2.me/theorems/630fa9df-eacd-4abe-9aa7-77412a606d5f
-- title:
--   Fpy: fpy round
-- statement:
--   The Fpy construction uses the fpy round property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L263-L263
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L263-L263

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.fpy_round (u : Num) : (fpy decode).arith (show ArithOp from .round) [u] = some u := by sorry
