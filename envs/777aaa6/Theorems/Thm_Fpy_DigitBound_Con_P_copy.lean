-- Prove2me | Theorems.Thm_Fpy_DigitBound_Con_P_copy
-- name    : Fpy.DigitBound.Con.P_copy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:22:28.703193+00:00
-- url     : https://prove2.me/theorems/bb9ce8f8-beee-450d-b766-ad3d97c08d42
-- title:
--   Con: P copy
-- statement:
--   The Con construction uses the P copy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L80-L83
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L80-L83

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Copy
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.Con.P_copy {c : Con} {a b n : ℕ} {hc : a ≤ c.head ∧ c.head < b} {han : a ≤ n}
    {ι : Asgn} : (c.copy a b n hc han).P ι ↔ c.P (ι ∘ shift a b n) := by sorry
