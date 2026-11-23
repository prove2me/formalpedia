-- Prove2me | Theorems.Thm_det_muller_lang_univ
-- name    : det_muller_lang_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:49:34.659232+00:00
-- url     : https://prove2.me/theorems/4868e936-9e60-4305-a1ac-9c0e7b51c643
-- title:
--   det muller lang univ: det muller lang univ
-- statement:
--   The language `univ` is a deterministic Muller language.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L45-L54
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L45-L54

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

theorem det_muller_lang_univ :
    DetMullerLang (univ : Set (Stream' A)) := by sorry
