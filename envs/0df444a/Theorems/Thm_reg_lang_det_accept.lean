-- Prove2me | Theorems.Thm_reg_lang_det_accept
-- name    : reg_lang_det_accept
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:17:01.66295+00:00
-- url     : https://prove2.me/theorems/44a74c66-bc38-4ba6-b483-ce0f11b18d1f
-- title:
--   reg lang det accept: reg lang det accept
-- statement:
--   A regular language is always accepted by a deterministic finite automaton.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L134-L139
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L134-L139

import Definitions.Def_AutomataTheory_Automata_Sum
import Definitions.Def_AutomataTheory_Automata_Prod
import Definitions.Def_AutomataTheory_Automata_PSet
import Definitions.Def_AutomataTheory_Automata_Concat
import Definitions.Def_AutomataTheory_Automata_Loop
import Definitions.Def_AutomataTheory_Automata_Congr
import Definitions.Def_AutomataTheory_Languages_RegLang
set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
open Classical
variable {A : Type}

theorem reg_lang_det_accept {L : Set (List A)} (h : RegLang L) :
    ∃ M : Automata.DA A, ∃ acc : Set M.State, Finite M.State ∧ L = M.toNA.AcceptedLang acc := by sorry
