-- Prove2me | Theorems.Thm_Mpfx_Special_neg_neg
-- name    : Mpfx.Special.neg_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T05:21:13.122841+00:00
-- url     : https://prove2.me/theorems/72cf7e8f-a57c-4520-b9d3-d59ac1133750
-- title:
--   Special: neg neg
-- statement:
--   The Special construction uses the neg neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L31-L32
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/Format/Defs.lean#L31-L32

import Definitions.Def_Mpfx_Dyadic
import Mathlib.Data.Int.Log
import Definitions.Def_Mpfx_Format_Defs
set_option autoImplicit true
open Mpfx

theorem Mpfx.Special.neg_neg (s : Special) : s.neg.neg = s := by sorry
