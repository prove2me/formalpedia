-- Prove2me | Theorems.Thm_Fpy_denotes_real
-- name    : Fpy.denotes_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:33:08.334259+00:00
-- url     : https://prove2.me/theorems/04ac07ec-6966-4b3b-8f8d-34c89ef6d527
-- title:
--   Fpy: denotes real
-- statement:
--   The Fpy construction uses the denotes real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L32-L33
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L32-L33

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}

theorem Fpy.denotes_real : Denotes Φ .real .real := by sorry
