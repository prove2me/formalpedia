-- Prove2me | Theorems.Thm_det_muller_lang_union
-- name    : det_muller_lang_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:50:01.887969+00:00
-- url     : https://prove2.me/theorems/2ec6cc7a-f048-40a9-b0cf-8317785e9526
-- title:
--   det muller lang union: det muller lang union
-- statement:
--   Deterministic Muller languages are closed under union.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L97-L112
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L97-L112

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

theorem det_muller_lang_union {L0 L1 : Set (Stream' A)}
    (h0 : DetMullerLang L0) (h1 : DetMullerLang L1) : DetMullerLang (L0 ∪ L1) := by sorry
