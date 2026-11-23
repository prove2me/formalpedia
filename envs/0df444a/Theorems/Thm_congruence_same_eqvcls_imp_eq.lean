-- Prove2me | Theorems.Thm_congruence_same_eqvcls_imp_eq
-- name    : congruence_same_eqvcls_imp_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:25:30.135259+00:00
-- url     : https://prove2.me/theorems/c05912e7-70e0-4a1e-a1c3-50d7dad60b5a
-- title:
--   congruence same eqvcls imp eq: congruence same eqvcls imp eq
-- statement:
--   A convenience lemma: Any two words in the same equivalence class of a congruence are congruent.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/Basic.lean#L86-L90
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Congruences/Basic.lean#L86-L90

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Languages_Basic
import Definitions.Def_AutomataTheory_Congruences_Basic
set_option autoImplicit true
open Function Set Stream'
open Classical
variable {A : Type}
variable {c : Congruence A}

theorem congruence_same_eqvcls_imp_eq {s : c.QuotType} {u u' : List A}
    (h : u ∈ c.EqvCls s) (h' : u' ∈ c.EqvCls s) : c.eq u u' := by sorry
