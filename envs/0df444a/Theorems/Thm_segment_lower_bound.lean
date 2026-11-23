-- Prove2me | Theorems.Thm_segment_lower_bound
-- name    : segment_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:45.721377+00:00
-- url     : https://prove2.me/theorems/71e5b62a-50a0-41b7-aec3-5cb717fbc9c4
-- title:
--   segment lower bound: segment lower bound
-- statement:
--   The segment lower bound construction uses the segment lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L80-L87
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L80-L87

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem segment_lower_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    φ (Segment φ k) ≤ k := by sorry
