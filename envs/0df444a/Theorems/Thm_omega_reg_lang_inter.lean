-- Prove2me | Theorems.Thm_omega_reg_lang_inter
-- name    : omega_reg_lang_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:41.613065+00:00
-- url     : https://prove2.me/theorems/289b99cd-ef81-463f-8165-2757800140f9
-- title:
--   omega reg lang inter: omega reg lang inter
-- statement:
--   ω-regular languages are closed under intersection.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L88-L105
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L88-L105

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

theorem omega_reg_lang_inter {L0 L1 : Set (Stream' A)}
    (h0 : OmegaRegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (L0 ∩ L1) := by sorry
