-- Prove2me | Theorems.Thm_det_muller_lang_empty
-- name    : det_muller_lang_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:49:38.61381+00:00
-- url     : https://prove2.me/theorems/6ad0967a-4db6-49fc-ba94-c5fa335619ec
-- title:
--   det muller lang empty: det muller lang empty
-- statement:
--   The language `∅` is a deterministic Muller language.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L36-L41
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L36-L41

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

theorem det_muller_lang_empty :
    DetMullerLang (∅ : Set (Stream' A)) := by sorry
