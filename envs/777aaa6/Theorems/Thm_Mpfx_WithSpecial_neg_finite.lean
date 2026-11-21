-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_neg_finite
-- name    : Mpfx.WithSpecial.neg_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:25.802246+00:00
-- url     : https://prove2.me/theorems/58fbeb7b-726e-47d2-95d7-632cc8bbf856
-- title:
--   With Special: neg finite
-- statement:
--   The With Special construction uses the neg finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L39-L40
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L39-L40

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.WithSpecial.neg_finite {α : Type} [Neg α] (a : α) :
    (WithSpecial.finite a).neg = .finite (-a) := by sorry

attribute [defeq] Mpfx.WithSpecial.neg_finite
