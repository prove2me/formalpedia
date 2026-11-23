-- Prove2me | Theorems.Thm_base_zero_shift
-- name    : base_zero_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:35.178541+00:00
-- url     : https://prove2.me/theorems/756f9192-e499-4542-bed5-87d6624a34d1
-- title:
--   base zero shift: base zero shift
-- statement:
--   The base zero shift construction uses the base zero shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L156-L158
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L156-L158

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set

theorem base_zero_shift (φ : ℕ → ℕ) :
    (φ · - φ 0) 0 = 0 := by sorry
