-- Prove2me | Theorems.Thm_congruence_saturates_compl
-- name    : congruence_saturates_compl
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:25:19.819071+00:00
-- url     : https://prove2.me/theorems/b20e08fc-73e7-4de6-8f3c-3a4ca5a1f04a
-- title:
--   congruence saturates compl: congruence saturates compl
-- statement:
--   If a congruence `c` saturates an ω-language `L`, then `c` saturates the complement of `L` as well.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/Basic.lean#L60-L68
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/Basic.lean#L60-L68

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Congruences_Basic
set_option autoImplicit true
open Function Set Stream'
open Classical
variable {A : Type}
variable {c : Congruence A}

theorem congruence_saturates_compl {L : Set (Stream' A)}
    (h_sat : c.Saturates L) : c.Saturates Lᶜ := by sorry
