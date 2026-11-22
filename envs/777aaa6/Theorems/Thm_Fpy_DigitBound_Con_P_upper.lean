-- Prove2me | Theorems.Thm_Fpy_DigitBound_Con_P_upper
-- name    : Fpy.DigitBound.Con.P_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:11:08.18501+00:00
-- url     : https://prove2.me/theorems/aa1c9f93-2ef6-4135-aaa6-88726290e035
-- title:
--   Con: P upper
-- statement:
--   The Con construction uses the P upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L329-L331
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L329-L331

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Mathlib.Order.WithBotTop
import Definitions.Def_Fpy_DigitBound_Defs
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.DigitBound.Con.P_upper {v : ℕ} {t : Term} {h : t.Below v} {ι : Asgn} :
    (Con.upper v t h).P ι ↔ ι v ≤ t.eval ι := by sorry
