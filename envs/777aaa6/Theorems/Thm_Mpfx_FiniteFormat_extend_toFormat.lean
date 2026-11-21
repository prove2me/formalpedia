-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
-- name    : Mpfx.FiniteFormat.extend_toFormat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:38:26.953238+00:00
-- url     : https://prove2.me/theorems/e80a0a66-2b05-451d-a7cb-3317bb2460b7
-- title:
--   Finite Format: extend to Format
-- statement:
--   The Finite Format construction uses the extend to Format property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L514-L515
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Containment.lean#L514-L515

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.extend_toFormat (F : FiniteFormat) k :
    (F.extend k).toFormat = F.toFormat.extend k := by sorry

attribute [defeq] Mpfx.FiniteFormat.extend_toFormat
