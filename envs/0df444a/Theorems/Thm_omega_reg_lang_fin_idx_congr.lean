-- Prove2me | Theorems.Thm_omega_reg_lang_fin_idx_congr
-- name    : omega_reg_lang_fin_idx_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:49:13.955316+00:00
-- url     : https://prove2.me/theorems/aec61f2e-a3a2-4a35-9bd8-d0c0d9512284
-- title:
--   omega reg lang fin idx congr: omega reg lang fin idx congr
-- statement:
--   If a congruence is of finite index, is ample, and saturates an ω-language `L`,
--   then `L` is ω-regular.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L206-L229
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/OmegaRegLang.lean#L206-L229

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

theorem omega_reg_lang_fin_idx_congr [Inhabited A] {c : Congruence A} {L : Set (Stream' A)}
    (h_fin : Finite (c.QuotType)) (h_amp : c.Ample) (h_sat : c.Saturates L) : OmegaRegLang L := by sorry
