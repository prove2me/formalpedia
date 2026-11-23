-- Prove2me | Theorems.Thm_acc_lang_congr
-- name    : acc_lang_congr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:26:43.122128+00:00
-- url     : https://prove2.me/theorems/1db29f28-4469-4449-a93e-4be15d4d3925
-- title:
--   acc lang congr: acc lang congr
-- statement:
--   The language accepted by `c.toDA` with a unique accepting state `s`
--   is exactly the equivalence class of `s`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Congr.lean#L55-L66
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Congr.lean#L55-L66

import Definitions.Def_AutomataTheory_Congruences_Basic
import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_Congr
set_option autoImplicit true
open Function Set Stream'
attribute [local instance_reducible] Stream' Congruence.QuotType
variable {A : Type}
attribute [local instance_reducible] Congruence.toDA
variable {c : Congruence A}

theorem acc_lang_congr [Inhabited A] (s : c.toDA.State) :
    c.toDA.toNA.AcceptedLang {s} = c.EqvCls s := by sorry
