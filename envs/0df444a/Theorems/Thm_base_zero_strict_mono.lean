-- Prove2me | Theorems.Thm_base_zero_strict_mono
-- name    : base_zero_strict_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:37.318804+00:00
-- url     : https://prove2.me/theorems/e6751bb3-c0f5-4487-b0eb-4fdb9d3c3645
-- title:
--   base zero strict mono: base zero strict mono
-- statement:
--   The base zero strict mono construction uses the base zero strict mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L160-L166
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L160-L166

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set

theorem base_zero_strict_mono {φ : ℕ → ℕ} (hm : StrictMono φ) :
    StrictMono (φ · - φ 0) := by sorry
