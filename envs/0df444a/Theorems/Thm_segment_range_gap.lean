-- Prove2me | Theorems.Thm_segment_range_gap
-- name    : segment_range_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:19:00.762121+00:00
-- url     : https://prove2.me/theorems/9c30c96b-0dbd-4afb-81b1-7afb30af1f27
-- title:
--   segment range gap: segment range gap
-- statement:
--   The segment range gap construction uses the segment range gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L102-L109
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L102-L109

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem segment_range_gap (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m < k) (hu : k < φ (m + 1)) : k ∉ range φ := by sorry
