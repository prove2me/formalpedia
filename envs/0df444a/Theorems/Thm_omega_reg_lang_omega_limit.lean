-- Prove2me | Theorems.Thm_omega_reg_lang_omega_limit
-- name    : omega_reg_lang_omega_limit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:49:17.512038+00:00
-- url     : https://prove2.me/theorems/16cf08e9-7259-408c-8af7-66863577d191
-- title:
--   omega reg lang omega limit: omega reg lang omega limit
-- statement:
--   The ω-limit of a regular language is ω-regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L141-L146
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L141-L146

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

theorem omega_reg_lang_omega_limit {L : Set (List A)}
    (h : RegLang L) : OmegaRegLang L↗ω := by sorry
