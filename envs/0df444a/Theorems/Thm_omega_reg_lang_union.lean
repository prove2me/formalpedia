-- Prove2me | Theorems.Thm_omega_reg_lang_union
-- name    : omega_reg_lang_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:45.509803+00:00
-- url     : https://prove2.me/theorems/7e68f921-c3ea-431d-a8ef-5d485a4f20fa
-- title:
--   omega reg lang union: omega reg lang union
-- statement:
--   ω-regular languages are closed under union.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L58-L73
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L58-L73

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

theorem omega_reg_lang_union {L0 L1 : Set (Stream' A)}
    (h0 : OmegaRegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (L0 ∪ L1) := by sorry
