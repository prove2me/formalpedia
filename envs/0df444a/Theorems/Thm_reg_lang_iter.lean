-- Prove2me | Theorems.Thm_reg_lang_iter
-- name    : reg_lang_iter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:20:42.22212+00:00
-- url     : https://prove2.me/theorems/3f87c285-7f77-450b-9c90-38626b70b390
-- title:
--   reg lang iter: reg lang iter
-- statement:
--   Regular languages are closed under Kleene star.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L192-L198
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/RegLang.lean#L192-L198

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

theorem reg_lang_iter [Inhabited A] {L : Set (List A)}
    (h : RegLang L) : RegLang L∗ := by sorry
