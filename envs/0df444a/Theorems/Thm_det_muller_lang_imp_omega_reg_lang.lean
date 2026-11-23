-- Prove2me | Theorems.Thm_det_muller_lang_imp_omega_reg_lang
-- name    : det_muller_lang_imp_omega_reg_lang
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:50:11.484061+00:00
-- url     : https://prove2.me/theorems/6535af23-f64c-4836-9af6-3b7a5b698de0
-- title:
--   det muller lang imp omega reg lang: det muller lang imp omega reg lang
-- statement:
--   Every deterministic Muller language is an ω-regular language.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L164-L175
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L164-L175

import Definitions.Def_AutomataTheory_Automata_DetConcat
import Definitions.Def_AutomataTheory_Automata_DetProd
import Definitions.Def_AutomataTheory_Languages_OmegaRegLang
import Definitions.Def_AutomataTheory_Languages_DetMullerLang
set_option autoImplicit true
open Function Set Stream'
open scoped Computability
attribute [local implicit_reducible] Stream'
attribute [local instance_reducible] Automata.DA.toNA Automata.DA.Prod
variable {A : Type}

theorem det_muller_lang_imp_omega_reg_lang [Inhabited A] {L : Set (Stream' A)}
    (h : DetMullerLang L) : OmegaRegLang L := by sorry
