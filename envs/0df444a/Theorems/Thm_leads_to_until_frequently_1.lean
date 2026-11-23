-- Prove2me | Theorems.Thm_leads_to_until_frequently_1
-- name    : leads_to_until_frequently_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:31.052805+00:00
-- url     : https://prove2.me/theorems/59989801-034f-439f-9a60-e24e8762714d
-- title:
--   leads to until frequently 1: leads to until frequently 1
-- statement:
--   The leads to until frequently 1 construction uses the leads to until frequently 1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L58-L77
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L58-L77

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal
set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}

theorem leads_to_until_frequently_1 {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∉ p) : LeadsTo xs p q := by sorry
