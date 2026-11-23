-- Prove2me | Theorems.Thm_omega_reg_lang_concat
-- name    : omega_reg_lang_concat
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:49:00.711307+00:00
-- url     : https://prove2.me/theorems/6f5db102-34c7-4035-88ef-71728d161c94
-- title:
--   omega reg lang concat: omega reg lang concat
-- statement:
--   The concatenation of a regular language and an ω-regular language is ω-regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L120-L127
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L120-L127

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

theorem omega_reg_lang_concat {L0 : Set (List A)} {L1 : Set (Stream' A)}
    (h0 : RegLang L0) (h1 : OmegaRegLang L1) : OmegaRegLang (L0 * L1) := by sorry
