-- Prove2me | Theorems.Thm_det_muller_lang_omega_limit
-- name    : det_muller_lang_omega_limit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:49:57.826813+00:00
-- url     : https://prove2.me/theorems/090b3947-4587-4584-b44e-2dc743a7fa8c
-- title:
--   det muller lang omega limit: det muller lang omega limit
-- statement:
--   The ω-limit of a regular language is a deterministic Muller language.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L127-L131
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L127-L131

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

theorem det_muller_lang_omega_limit {L : Set (List A)}
    (h : RegLang L) : DetMullerLang L↗ω := by sorry
