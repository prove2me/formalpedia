-- Prove2me | Theorems.Thm_omega_reg_lang_univ
-- name    : omega_reg_lang_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:56.469799+00:00
-- url     : https://prove2.me/theorems/ef6fa087-1253-474d-a603-898b4e3d8975
-- title:
--   omega reg lang univ: omega reg lang univ
-- statement:
--   The language `univ` is ω-regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L46-L54
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L46-L54

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

theorem omega_reg_lang_univ :
    OmegaRegLang (univ : Set (Stream' A)) := by sorry
