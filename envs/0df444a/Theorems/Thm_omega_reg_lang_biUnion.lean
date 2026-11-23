-- Prove2me | Theorems.Thm_omega_reg_lang_biUnion
-- name    : omega_reg_lang_biUnion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:48:58.945121+00:00
-- url     : https://prove2.me/theorems/8e5cde37-4ba2-4d9f-8e42-a1f11399213d
-- title:
--   omega reg lang bi Union: omega reg lang bi Union
-- statement:
--   ω-regular languages are closed under finite bounded indexed union.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L77-L84
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L77-L84

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

theorem omega_reg_lang_biUnion {I : Type} [Finite I] {s : Set I} {L : I → Set (Stream' A)}
    (h : ∀ i ∈ s, OmegaRegLang (L i)) : OmegaRegLang (⋃ i ∈ s, L i) := by sorry
