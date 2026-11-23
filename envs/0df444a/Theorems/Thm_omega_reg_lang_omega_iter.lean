-- Prove2me | Theorems.Thm_omega_reg_lang_omega_iter
-- name    : omega_reg_lang_omega_iter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:49:05.959738+00:00
-- url     : https://prove2.me/theorems/dee68bb5-a913-49f9-840b-3f523c78d877
-- title:
--   omega reg lang omega iter: omega reg lang omega iter
-- statement:
--   The ω-power of a regular language is ω-regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L131-L137
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L131-L137

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

theorem omega_reg_lang_omega_iter {L : Set (List A)}
    (h : RegLang L) : OmegaRegLang L^ω := by sorry
