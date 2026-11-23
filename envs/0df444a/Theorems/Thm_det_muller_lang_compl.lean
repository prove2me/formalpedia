-- Prove2me | Theorems.Thm_det_muller_lang_compl
-- name    : det_muller_lang_compl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:52:13.232316+00:00
-- url     : https://prove2.me/theorems/d1cfacb2-8e32-483e-a1ab-2997c4485cd7
-- title:
--   det muller lang compl: det muller lang compl
-- statement:
--   Deterministic Muller languages are closed under complementation.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L58-L63
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Languages/DetMullerLang.lean#L58-L63

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

theorem det_muller_lang_compl {L : Set (Stream' A)}
    (h : DetMullerLang L) : DetMullerLang Lᶜ := by sorry
