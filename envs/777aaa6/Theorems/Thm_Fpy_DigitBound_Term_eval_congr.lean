-- Prove2me | Theorems.Thm_Fpy_DigitBound_Term_eval_congr
-- name    : Fpy.DigitBound.Term.eval_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:10:36.453015+00:00
-- url     : https://prove2.me/theorems/5fecce71-5ff3-4910-a63f-7e256946b855
-- title:
--   Term: eval congr
-- statement:
--   The Term construction uses the eval congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L98-L106
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L98-L106

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Mathlib.Order.WithBotTop
import Definitions.Def_Fpy_DigitBound_Defs
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx

theorem Fpy.DigitBound.Term.eval_congr {n : ℕ} {ι ι' : Asgn} (h : ∀ x < n, ι x = ι' x) :
    ∀ {t : Term}, t.Below n → t.eval ι = t.eval ι'
  := by sorry
