-- Prove2me | Theorems.Thm_omega_reg_lang_fin_idx_congr_compl
-- name    : omega_reg_lang_fin_idx_congr_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:49:13.791993+00:00
-- url     : https://prove2.me/theorems/2ddb0f13-c624-4025-8813-1aca44cf6b43
-- title:
--   omega reg lang fin idx congr compl: omega reg lang fin idx congr compl
-- statement:
--   If a congruence is of finite index, is ample, and saturates an ω-language `L`,
--   then the complement of `L` is ω-regular as well.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L234-L237
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L234-L237

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

theorem omega_reg_lang_fin_idx_congr_compl [Inhabited A] {c : Congruence A} {L : Set (Stream' A)}
    (h_fin : Finite (c.QuotType)) (h_amp : c.Ample) (h_sat : c.Saturates L) : OmegaRegLang Lᶜ := by sorry
