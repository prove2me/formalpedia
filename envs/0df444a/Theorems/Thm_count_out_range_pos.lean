-- Prove2me | Theorems.Thm_count_out_range_pos
-- name    : count_out_range_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:57.081482+00:00
-- url     : https://prove2.me/theorems/7647eddb-967f-4ddd-91e1-268a0dea3e1d
-- title:
--   count out range pos: count out range pos
-- statement:
--   The count out range pos construction uses the count out range pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L58-L65
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L58-L65

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem count_out_range_pos (h0 : φ 0 = 0) (n : ℕ) (hn : n ∉ range φ) :
    Nat.count (· ∈ range φ) n > 0 := by sorry
