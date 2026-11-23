-- Prove2me | Theorems.Thm_segment_zero
-- name    : segment_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:16:46.588896+00:00
-- url     : https://prove2.me/theorems/126308bc-ee5c-4197-8ba0-bfec7dfff9d7
-- title:
--   segment zero: segment zero
-- statement:
--   The segment zero construction uses the segment zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L97-L100
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L97-L100

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem segment_zero (hm : StrictMono φ) (h0 : φ 0 = 0) :
    Segment φ 0 = 0 := by sorry
