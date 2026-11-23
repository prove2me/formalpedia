-- Prove2me | Theorems.Thm_omega_reg_lang_biInter
-- name    : omega_reg_lang_biInter
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:49:02.748787+00:00
-- url     : https://prove2.me/theorems/d5325d1b-0212-4213-9b3f-df5ca324450a
-- title:
--   omega reg lang bi Inter: omega reg lang bi Inter
-- statement:
--   ω-regular languages are closed under finite bounded indexed intersection.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L109-L116
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L109-L116

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

theorem omega_reg_lang_biInter {I : Type} [Finite I] {s : Set I} {L : I → Set (Stream' A)}
    (h : ∀ i ∈ s, OmegaRegLang (L i)) : OmegaRegLang (⋂ i ∈ s, L i) := by sorry
