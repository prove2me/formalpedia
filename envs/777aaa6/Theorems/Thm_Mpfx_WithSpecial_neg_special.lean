-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_neg_special
-- name    : Mpfx.WithSpecial.neg_special
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:24.352818+00:00
-- url     : https://prove2.me/theorems/4e9a879d-c41d-4ef7-bae1-3522e93a9770
-- title:
--   With Special: neg special
-- statement:
--   The With Special construction uses the neg special property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L42-L43
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L42-L43

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.WithSpecial.neg_special {α : Type} [Neg α] (s : Special) :
    (WithSpecial.special s : WithSpecial α).neg = .special s.neg := by sorry

attribute [defeq] Mpfx.WithSpecial.neg_special
