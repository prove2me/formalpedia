-- Prove2me | Theorems.Thm_reg_lang_univ
-- name    : reg_lang_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:27.420038+00:00
-- url     : https://prove2.me/theorems/936caca1-8fdd-43ae-8bcb-59d34dccc7b1
-- title:
--   reg lang univ: reg lang univ
-- statement:
--   The language `univ` is regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L63-L70
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L63-L70

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

theorem reg_lang_univ [Inhabited A] :
    RegLang (univ : Set (List A)) := by sorry
