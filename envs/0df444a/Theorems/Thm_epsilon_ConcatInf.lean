-- Prove2me | Theorems.Thm_epsilon_ConcatInf
-- name    : epsilon_ConcatInf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:34:00.744724+00:00
-- url     : https://prove2.me/theorems/6ee42a14-0722-49b6-8f6d-20b48784625a
-- title:
--   epsilon Concat Inf: epsilon Concat Inf
-- statement:
--   The epsilon Concat Inf construction uses the epsilon Concat Inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L130-L135
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/Basic.lean#L130-L135

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}

theorem epsilon_ConcatInf {L : Set (Stream' A)} :
    ({[]} : Set (List A)) * L = L := by sorry
