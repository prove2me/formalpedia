-- Prove2me | Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
-- name    : Mpfx.FiniteFormat.unbounded_p
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:22:47.582658+00:00
-- url     : https://prove2.me/theorems/6bb6e0ad-fd73-4b65-97fa-d079acade9cb
-- title:
--   Finite Format: unbounded p
-- statement:
--   The Finite Format construction uses the unbounded p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L397-L397
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L397-L397

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat

theorem Mpfx.FiniteFormat.unbounded_p (F : FiniteFormat) : F.unbounded.p = F.p := by sorry

attribute [defeq] Mpfx.FiniteFormat.unbounded_p
