-- Prove2me | Theorems.Thm_reg_lang_empty
-- name    : reg_lang_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:20:26.315662+00:00
-- url     : https://prove2.me/theorems/d15cfdbb-8efd-4a18-ba16-80ec0892fcbc
-- title:
--   reg lang empty: reg lang empty
-- statement:
--   The language `∅` is regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L38-L44
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L38-L44

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

theorem reg_lang_empty :
    RegLang (∅ : Set (List A)) := by sorry
