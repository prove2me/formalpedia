-- Prove2me | Theorems.Thm_reg_lang_concat_e
-- name    : reg_lang_concat_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:47.777709+00:00
-- url     : https://prove2.me/theorems/fe80f727-adc4-4eeb-919c-a6b7489768a6
-- title:
--   reg lang concat e: reg lang concat e
-- statement:
--   Helper lemma for `reg_lang_concat` below.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L168-L180
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L168-L180

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

theorem reg_lang_concat_e {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) (h_e : [] ∈ L1) : RegLang (L0 * L1) := by sorry
