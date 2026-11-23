-- Prove2me | Theorems.Thm_reg_lang_union
-- name    : reg_lang_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:30.970243+00:00
-- url     : https://prove2.me/theorems/8f9a5fb5-31f4-46cf-bc5f-df847535db34
-- title:
--   reg lang union: reg lang union
-- statement:
--   Regular languages are closed under union.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L74-L89
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L74-L89

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

theorem reg_lang_union {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) : RegLang (L0 ∪ L1) := by sorry
