-- Prove2me | Theorems.Thm_strict_mono_infinite
-- name    : strict_mono_infinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:11:33.75125+00:00
-- url     : https://prove2.me/theorems/acfce27a-c1cf-4543-9f55-cd374b741ad0
-- title:
--   strict mono infinite: strict mono infinite
-- statement:
--   The strict mono infinite construction uses the strict mono infinite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L30-L32
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L30-L32

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem strict_mono_infinite (hm : StrictMono φ) :
    (range φ).Infinite := by sorry
