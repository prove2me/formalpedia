-- Prove2me | Theorems.Thm_automaton_congr_run
-- name    : automaton_congr_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:26:42.256958+00:00
-- url     : https://prove2.me/theorems/c586d4f9-c81c-4a75-b422-3c52db6e2463
-- title:
--   automaton congr run: automaton congr run
-- statement:
--   Running `c.toDA` on input `as` ends in state `⟦ as ⟧`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Congr.lean#L44-L50
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Automata/Congr.lean#L44-L50

import Definitions.Def_AutomataTheory_Congruences_Basic
import Definitions.Def_AutomataTheory_Automata_Det
import Definitions.Def_AutomataTheory_Automata_Congr
set_option autoImplicit true
open Function Set Stream'
attribute [local instance_reducible] Stream' Congruence.QuotType
variable {A : Type}
attribute [local instance_reducible] Congruence.toDA
variable {c : Congruence A}

theorem automaton_congr_run (as : Stream' A) (n : ℕ) :
    c.toDA.DetRun as n = ⟦ as.extract 0 n ⟧ := by sorry
