-- Prove2me | Theorems.Thm_reg_lang_biUnion
-- name    : reg_lang_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:20:31.810973+00:00
-- url     : https://prove2.me/theorems/f35ecb8f-5373-4326-b177-380fd3ea6ae7
-- title:
--   reg lang bi Union: reg lang bi Union
-- statement:
--   Regular languages are closed under finite bounded indexed union.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L93-L100
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L93-L100

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

theorem reg_lang_biUnion {I : Type} [Finite I] {s : Set I} {L : I → Set (List A)}
    (h : ∀ i ∈ s, RegLang (L i)) : RegLang (⋃ i ∈ s, L i) := by sorry
