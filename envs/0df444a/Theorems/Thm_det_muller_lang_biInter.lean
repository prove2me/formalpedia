-- Prove2me | Theorems.Thm_det_muller_lang_biInter
-- name    : det_muller_lang_biInter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:52:15.803139+00:00
-- url     : https://prove2.me/theorems/4f7f1856-127f-453a-8072-d4cc3c76c3c6
-- title:
--   det muller lang bi Inter: det muller lang bi Inter
-- statement:
--   Deterministic Muller languages are closed under finite bounded indexed intersection.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L86-L93
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L86-L93

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

theorem det_muller_lang_biInter {I : Type} [Finite I] {s : Set I} {L : I → Set (Stream' A)}
    (h : ∀ i ∈ s, DetMullerLang (L i)) : DetMullerLang (⋂ i ∈ s, L i) := by sorry
