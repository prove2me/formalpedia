-- Prove2me | Theorems.Thm_empty_ConcatInf
-- name    : empty_ConcatInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:24:36.945801+00:00
-- url     : https://prove2.me/theorems/2fc2a397-cf52-4cd7-8ff3-58ce9e2ee001
-- title:
--   empty Concat Inf: empty Concat Inf
-- statement:
--   The empty Concat Inf construction uses the empty Concat Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L124-L128
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L124-L128

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem empty_ConcatInf {L : Set (Stream' A)} :
    (∅ : Set (List A)) * L = ∅ := by sorry
