-- Prove2me | Theorems.Thm_Mpfx_WithSpecial_neg_neg
-- name    : Mpfx.WithSpecial.neg_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:30.927091+00:00
-- url     : https://prove2.me/theorems/c8bde6ce-7966-42f3-92b5-0234813ac084
-- title:
--   With Special: neg neg
-- statement:
--   The With Special construction uses the neg neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L45-L47
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L45-L47

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.WithSpecial.neg_neg {α : Type} [InvolutiveNeg α] (v : WithSpecial α) :
    v.neg.neg = v := by sorry
