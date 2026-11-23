-- Prove2me | Theorems.Thm_det_muller_lang_biUnion
-- name    : det_muller_lang_biUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:49:42.826501+00:00
-- url     : https://prove2.me/theorems/42fd7edf-70e7-46ec-ac29-232ed9dd96ed
-- title:
--   det muller lang bi Union: det muller lang bi Union
-- statement:
--   Deterministic Muller languages are closed under finite bounded indexed union.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L116-L123
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L116-L123

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

theorem det_muller_lang_biUnion {I : Type} [Finite I] {s : Set I} {L : I → Set (Stream' A)}
    (h : ∀ i ∈ s, DetMullerLang (L i)) : DetMullerLang (⋃ i ∈ s, L i) := by sorry
