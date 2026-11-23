-- Prove2me | Theorems.Thm_det_muller_lang_inter
-- name    : det_muller_lang_inter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:49:44.121653+00:00
-- url     : https://prove2.me/theorems/6472d3bb-1981-4f4f-a97c-93b51eeffa3c
-- title:
--   det muller lang inter: det muller lang inter
-- statement:
--   Deterministic Muller languages are closed under intersection.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L67-L82
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L67-L82

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

theorem det_muller_lang_inter {L0 L1 : Set (Stream' A)}
    (h0 : DetMullerLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 ∩ L1) := by sorry
