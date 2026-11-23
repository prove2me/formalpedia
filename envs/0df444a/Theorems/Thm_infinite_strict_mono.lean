-- Prove2me | Theorems.Thm_infinite_strict_mono
-- name    : infinite_strict_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:22:27.188265+00:00
-- url     : https://prove2.me/theorems/3a2e94fb-0e90-4c8e-a5ae-5104b3b29ccd
-- title:
--   infinite strict mono: infinite strict mono
-- statement:
--   The infinite strict mono construction uses the infinite strict mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L34-L38
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L34-L38

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem infinite_strict_mono {ns : Set ℕ} (h : ns.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ range φ = ns := by sorry
