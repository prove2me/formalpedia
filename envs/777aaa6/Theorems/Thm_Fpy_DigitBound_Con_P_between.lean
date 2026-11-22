-- Prove2me | Theorems.Thm_Fpy_DigitBound_Con_P_between
-- name    : Fpy.DigitBound.Con.P_between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:10:58.030955+00:00
-- url     : https://prove2.me/theorems/9369ee00-9cb9-4e33-933b-4f5b6fc1536e
-- title:
--   Con: P between
-- statement:
--   The Con construction uses the P between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L348-L350
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L348-L350

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Mathlib.Order.WithBotTop
import Definitions.Def_Fpy_DigitBound_Defs
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.DigitBound.Con.P_between {v : ℕ} {a b : ℤ} {h : a ≤ b} {ι : Asgn} :
    (Con.between v a b h).P ι ↔ (a : EInt) ≤ ι v ∧ ι v ≤ b := by sorry
