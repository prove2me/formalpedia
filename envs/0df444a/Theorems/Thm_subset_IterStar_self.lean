-- Prove2me | Theorems.Thm_subset_IterStar_self
-- name    : subset_IterStar_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:34:22.711299+00:00
-- url     : https://prove2.me/theorems/a51166cd-eb27-495c-beb7-580de68cb2e2
-- title:
--   subset Iter Star self: subset Iter Star self
-- statement:
--   The subset Iter Star self construction uses the subset Iter Star self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L160-L165
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L160-L165

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem subset_IterStar_self (L : Set (List A)) :
    L ⊆ L∗ := by sorry
