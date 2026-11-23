-- Prove2me | Theorems.Thm_segment_upper_bound
-- name    : segment_upper_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:11:45.359784+00:00
-- url     : https://prove2.me/theorems/554ccb9a-e64e-471c-a42b-cc8c4ca5d9d6
-- title:
--   segment upper bound: segment upper bound
-- statement:
--   The segment upper bound construction uses the segment upper bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L73-L78
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L73-L78

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem segment_upper_bound (hm : StrictMono φ) (h0 : φ 0 = 0) (k : ℕ) :
    k < φ (Segment φ k + 1) := by sorry
