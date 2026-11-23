-- Prove2me | Theorems.Thm_omega_reg_lang_empty
-- name    : omega_reg_lang_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:50.628762+00:00
-- url     : https://prove2.me/theorems/5e19b647-ba28-4722-aa44-c454ebb8b2b2
-- title:
--   omega reg lang empty: omega reg lang empty
-- statement:
--   The language `∅` is ω-regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L37-L42
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L37-L42

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

theorem omega_reg_lang_empty :
    OmegaRegLang (∅ : Set (Stream' A)) := by sorry
