-- Prove2me | Theorems.Thm_antitone_fin_eventually
-- name    : antitone_fin_eventually
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:21:36.174582+00:00
-- url     : https://prove2.me/theorems/9f7d0d1f-4771-49ee-b711-a117513c5f36
-- title:
--   antitone fin eventually: antitone fin eventually
-- statement:
--   The antitone fin eventually construction uses the antitone fin eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L175-L183
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Basic.lean#L175-L183

import Definitions.Def_AutomataTheory_Mathlib_Imports
import Definitions.Def_AutomataTheory_Sequences_Basic
set_option autoImplicit true
open Function Set Option Stream'

theorem antitone_fin_eventually {n : ℕ} {f : ℕ → Fin n} (h : Antitone f) :
    ∃ i : Fin n, ∃ m, ∀ k ≥ m, f k = i := by sorry
