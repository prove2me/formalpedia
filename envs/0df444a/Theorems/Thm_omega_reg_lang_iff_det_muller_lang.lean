-- Prove2me | Theorems.Thm_omega_reg_lang_iff_det_muller_lang
-- name    : omega_reg_lang_iff_det_muller_lang
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:52:44.162804+00:00
-- url     : https://prove2.me/theorems/8bbfa44d-cf2e-45f1-9ca4-3983925d3126
-- title:
--   omega reg lang iff det muller lang: omega reg lang iff det muller lang
-- statement:
--   McNaughton's theorem: An ω-language is ω-regular
--   if and only if it is deterministic Muller.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L194-L198
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L194-L198

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

theorem omega_reg_lang_iff_det_muller_lang [Inhabited A] {L : Set (Stream' A)} :
    OmegaRegLang L ↔ DetMullerLang L := by sorry
