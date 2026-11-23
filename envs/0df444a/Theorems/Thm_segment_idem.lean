-- Prove2me | Theorems.Thm_segment_idem
-- name    : segment_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:12:49.208092+00:00
-- url     : https://prove2.me/theorems/69cfd165-996e-4b07-902c-c7316447d757
-- title:
--   segment idem: segment idem
-- statement:
--   The segment idem construction uses the segment idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L89-L95
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L89-L95

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem segment_idem (hm : StrictMono φ) (k : ℕ) :
    Segment φ (φ k) = k := by sorry
