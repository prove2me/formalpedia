-- Prove2me | Theorems.Thm_leads_to_cases
-- name    : leads_to_cases
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:28:31.429823+00:00
-- url     : https://prove2.me/theorems/fdd63b54-b8cd-4f69-85c0-b78a05817218
-- title:
--   leads to cases: leads to cases
-- statement:
--   The leads to cases construction uses the leads to cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L47-L56
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L47-L56

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal
set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}

theorem leads_to_cases {p q r s : Set X}
    (h1 : LeadsTo xs (p ∩ q) r) (h2 : LeadsTo xs (p ∩ qᶜ) s) : LeadsTo xs p (r ∪ s) := by sorry
