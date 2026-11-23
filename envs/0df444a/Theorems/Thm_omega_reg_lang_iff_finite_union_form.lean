-- Prove2me | Theorems.Thm_omega_reg_lang_iff_finite_union_form
-- name    : omega_reg_lang_iff_finite_union_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:48:46.575129+00:00
-- url     : https://prove2.me/theorems/a3dca705-e7d3-4a8f-899a-e7f8b84242c1
-- title:
--   omega reg lang iff finite union form: omega reg lang iff finite union form
-- statement:
--   An ω-language is ω-regular if and only if it is the finite union of sets
--   of the form `U * V^ω`, where all `U`s and `V`s are regular languages.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L151-L201
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L151-L201

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

theorem omega_reg_lang_iff_finite_union_form [Inhabited A] {L : Set (Stream' A)} :
    OmegaRegLang L ↔
    ∃ n : ℕ, ∃ U V : Fin n → Set (List A),
      (∀ i, RegLang (U i) ∧ RegLang (V i)) ∧ L = ⋃ i, (U i) * (V i)^ω := by sorry
