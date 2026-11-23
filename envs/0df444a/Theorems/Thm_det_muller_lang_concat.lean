-- Prove2me | Theorems.Thm_det_muller_lang_concat
-- name    : det_muller_lang_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:50:19.910505+00:00
-- url     : https://prove2.me/theorems/3ca63ed3-5700-46e4-8b28-a7b179f518b7
-- title:
--   det muller lang concat: det muller lang concat
-- statement:
--   The concatenation of a regular language and a deterministic Muller language
--   is a deterministic Muller language.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L136-L160
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L136-L160

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

theorem det_muller_lang_concat {L0 : Set (List A)} {L1 : Set (Stream' A)}
    (h0 : RegLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 * L1) := by sorry
