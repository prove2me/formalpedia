-- Prove2me | Theorems.Thm_leads_to_until_frequently_2
-- name    : leads_to_until_frequently_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:28:36.629791+00:00
-- url     : https://prove2.me/theorems/3baa2557-915f-4e78-b10e-28d9852135d1
-- title:
--   leads to until frequently 2: leads to until frequently 2
-- statement:
--   The leads to until frequently 2 construction uses the leads to until frequently 2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L79-L99
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Temporal.lean#L79-L99

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Temporal
set_option autoImplicit true
open Function Set Filter Stream'
variable {X : Type*} {xs : Stream' X}

theorem leads_to_until_frequently_2 {p q : Set X}
    (h1 : Step xs (p ∩ qᶜ) p) (h2 : ∃ᶠ k in atTop, xs k ∈ q) : LeadsTo xs p (p ∩ q) := by sorry
