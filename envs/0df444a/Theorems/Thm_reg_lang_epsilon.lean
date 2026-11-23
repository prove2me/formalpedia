-- Prove2me | Theorems.Thm_reg_lang_epsilon
-- name    : reg_lang_epsilon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:08.856424+00:00
-- url     : https://prove2.me/theorems/81fb65a1-80b2-4843-b5ac-33044024951d
-- title:
--   reg lang epsilon: reg lang epsilon
-- statement:
--   The language `{[]}` is regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L48-L59
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L48-L59

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

theorem reg_lang_epsilon [Inhabited A] :
    RegLang ({[]} : Set (List A)) := by sorry
