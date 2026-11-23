-- Prove2me | Theorems.Thm_congruence_ample_saturates_union
-- name    : congruence_ample_saturates_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:25:19.01661+00:00
-- url     : https://prove2.me/theorems/8f91f8a2-f1da-42a8-84a0-1cb0aa4a75e7
-- title:
--   congruence ample saturates union: congruence ample saturates union
-- statement:
--   If a congruence `c` is ample and saturates an ω-language `L`, then `L` is the union of ω-languages
--       of the form `U * V^ω`, where `U` and `V` are equivalence classes of `c`.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/Basic.lean#L73-L82
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/Basic.lean#L73-L82

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Congruences_Basic
set_option autoImplicit true
open Function Set Stream'
open Classical
variable {A : Type}
variable {c : Congruence A}

theorem congruence_ample_saturates_union {L : Set (Stream' A)}
    (h_amp : c.Ample) (h_sat : c.Saturates L) :
    L =  ⋃ s, ⋃ t, if (c.ConcatOmegaLang s t ∩ L).Nonempty then c.ConcatOmegaLang s t else ∅ := by sorry
