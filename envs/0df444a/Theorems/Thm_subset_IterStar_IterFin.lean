-- Prove2me | Theorems.Thm_subset_IterStar_IterFin
-- name    : subset_IterStar_IterFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:17:40.922906+00:00
-- url     : https://prove2.me/theorems/06649988-21db-4b86-9728-1eb3ba671d76
-- title:
--   subset Iter Star Iter Fin: subset Iter Star Iter Fin
-- statement:
--   The subset Iter Star Iter Fin construction uses the subset Iter Star Iter Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L152-L154
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L152-L154

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem subset_IterStar_IterFin (L : Set (List A)) (n : ℕ) :
    L ^ n ⊆ L∗ := by sorry
