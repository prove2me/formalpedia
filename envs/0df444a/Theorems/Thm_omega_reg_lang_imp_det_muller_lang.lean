-- Prove2me | Theorems.Thm_omega_reg_lang_imp_det_muller_lang
-- name    : omega_reg_lang_imp_det_muller_lang
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:50:18.556473+00:00
-- url     : https://prove2.me/theorems/505f0a65-c199-4b5f-843f-62abe6543f94
-- title:
--   omega reg lang imp det muller lang: omega reg lang imp det muller lang
-- statement:
--   Every deterministic Muller language is an ω-regular language.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L179-L189
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L179-L189

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

theorem omega_reg_lang_imp_det_muller_lang [Inhabited A] {L : Set (Stream' A)}
    (h : OmegaRegLang L) : DetMullerLang L := by sorry
