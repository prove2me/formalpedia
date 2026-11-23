-- Prove2me | Theorems.Thm_reg_lang_compl
-- name    : reg_lang_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:18:21.003871+00:00
-- url     : https://prove2.me/theorems/66001f06-36b0-4ba5-8297-574bbe347db1
-- title:
--   reg lang compl: reg lang compl
-- statement:
--   Regular languages are closed under complementation.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L143-L148
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L143-L148

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

theorem reg_lang_compl [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang Lᶜ := by sorry
