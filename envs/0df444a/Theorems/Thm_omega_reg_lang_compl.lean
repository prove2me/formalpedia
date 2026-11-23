-- Prove2me | Theorems.Thm_omega_reg_lang_compl
-- name    : omega_reg_lang_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:49:21.849015+00:00
-- url     : https://prove2.me/theorems/fca02a5f-104f-4831-a2b6-941a059a8203
-- title:
--   omega reg lang compl: omega reg lang compl
-- statement:
--   ω-regular languages are closed under complementation.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L241-L245
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L241-L245

import Definitions.Def_AutomataTheory_Automata_OI2
import Definitions.Def_AutomataTheory_Congruences_BuchiCongr
import Definitions.Def_AutomataTheory_Languages_ChouekaLemma
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
set_option autoImplicit true
open Function Set Filter Sum Stream'
open scoped Computability
attribute [local implicit_reducible] Stream' Set.ncard
attribute [local instance_reducible] Automata.NA.OI2 Automata.NA.addHist Automata.NA.Prod
open Classical
variable {A : Type}

theorem omega_reg_lang_compl [Inhabited A] {L : Set (Stream' A)}
    (h : OmegaRegLang L) : OmegaRegLang Lᶜ := by sorry
