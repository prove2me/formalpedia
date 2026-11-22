-- Prove2me | Theorems.Thm_Fpy_DigitBound_Term_Below_rename_shift
-- name    : Fpy.DigitBound.Term.Below.rename_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:25:01.186934+00:00
-- url     : https://prove2.me/theorems/e8cbb6dc-242c-4c30-bd75-37767847c9f2
-- title:
--   Below: rename shift
-- statement:
--   The Below construction uses the rename shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L33-L44
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Copy.lean#L33-L44

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Copy
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.Term.Below.rename_shift {a b n : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    ∀ {t : Term}, t.Below b → (t.rename (shift a b n)).Below (n + (b - a)) := by sorry
