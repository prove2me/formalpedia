-- Prove2me | Theorems.Thm_leads_to_step
-- name    : leads_to_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:31.257822+00:00
-- url     : https://prove2.me/theorems/2007f105-f586-4599-a490-67f3738c10df
-- title:
--   leads to step: leads to step
-- statement:
--   The leads to step construction uses the leads to step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L31-L36
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L31-L36

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal
set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}

theorem leads_to_step {p q : Set X}
    (h : Step xs p q) : LeadsTo xs p q := by sorry
