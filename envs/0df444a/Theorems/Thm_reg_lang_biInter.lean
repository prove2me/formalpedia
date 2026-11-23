-- Prove2me | Theorems.Thm_reg_lang_biInter
-- name    : reg_lang_biInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:44:10.805951+00:00
-- url     : https://prove2.me/theorems/da242ea4-b111-4373-9784-19f8c85fc038
-- title:
--   reg lang bi Inter: reg lang bi Inter
-- statement:
--   Regular languages are closed under finite bounded indexed intersection.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L123-L130
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L123-L130

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

theorem reg_lang_biInter [Inhabited A] {I : Type} [Finite I] {s : Set I} {L : I → Set (List A)}
    (h : ∀ i ∈ s, RegLang (L i)) : RegLang (⋂ i ∈ s, L i) := by sorry
