-- Prove2me | Theorems.Thm_reg_lang_concat_ne
-- name    : reg_lang_concat_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:30:41.242224+00:00
-- url     : https://prove2.me/theorems/93f10262-6ed9-4bf3-bde4-95332f8b9f4e
-- title:
--   reg lang concat ne: reg lang concat ne
-- statement:
--   Helper lemma for `reg_lang_concat` below.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L152-L164
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L152-L164

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

theorem reg_lang_concat_ne {L0 L1 : Set (List A)}
    (h0 : RegLang L0) (h1 : RegLang L1) (h_ne : [] ∉ L1) : RegLang (L0 * L1) := by sorry
