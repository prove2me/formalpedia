-- Prove2me | Theorems.Thm_Fpy_DigitBound_Con_P_lower
-- name    : Fpy.DigitBound.Con.P_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:10:35.772096+00:00
-- url     : https://prove2.me/theorems/2679f238-36e0-453e-829a-652647e37bd9
-- title:
--   Con: P lower
-- statement:
--   The Con construction uses the P lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L316-L318
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Defs.lean#L316-L318

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Mathlib.Order.WithBotTop
import Definitions.Def_Fpy_DigitBound_Defs
set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}

theorem Fpy.DigitBound.Con.P_lower {v : ℕ} {t : Term} {h : t.Below v} {ι : Asgn} :
    (Con.lower v t h).P ι ↔ t.eval ι ≤ ι v := by sorry
